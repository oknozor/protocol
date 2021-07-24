use crate::format::{self, Format};

use proc_macro2::{Span, TokenStream};
use syn;
use syn::{ExprPath, ExprBinary, ExprUnary, Expr, MetaList, NestedMeta, MetaNameValue};
use quote::ToTokens;

const REPR: &'static str = "repr";
const SKIP_IF: &'static str = "skip_if";
const FIXED_LENGTH: &'static str = "fixed_length";
const LENGTH_PREFIX: &'static str = "length_prefix";
const DISCRIMINATOR: &'static str = "discriminator";
const DISCRIMINANT: &'static str = "discriminant";

#[derive(Default)]
pub struct AttributeContainer {
    pub discriminator: Option<Protocol>,
    pub discriminant: Option<Protocol>,
    pub length: Option<Protocol>,
    pub skip_if: Option<Protocol>,
}

impl AttributeContainer {
    pub fn set_dicriminator(&mut self, discriminator: Protocol) {
        debug_assert!(matches!(discriminator, Protocol::Discriminator(_)));
        if let Some(_) = &self.discriminator {
            panic!("duplicate protocol attribute `{}`", DISCRIMINATOR)
        } else {
            self.discriminator = Some(discriminator);
        }
    }

    pub fn set_discriminant(&mut self, discriminant: Protocol) {
        debug_assert!(matches!(discriminant, Protocol::DiscriminantFormat(_)));
        if let Some(_) = &self.discriminant {
            panic!("duplicate protocol attribute `{}`", DISCRIMINANT)
        } else {
            self.discriminant = Some(discriminant);
        }
    }

    pub fn set_skip_if(&mut self, skip_if: Protocol) {
        debug_assert!(matches!(skip_if, Protocol::SkipIf(_)));
        if let Some(_) = &self.skip_if {
            panic!("duplicate protocol attribute `{}`", SKIP_IF)
        } else {
            self.skip_if = Some(skip_if);
        }
    }

    pub fn set_length(&mut self, length: Protocol) {
        debug_assert!(matches!(length, Protocol::LengthPrefix {..} | Protocol::FixedLength(_) | Protocol::FixedLengthPath(_) ));
        if let Some(l) = &self.length {
            match l {
                Protocol::LengthPrefix { .. } => panic!("duplicate protocol attribute `{}`", LENGTH_PREFIX),
                Protocol::FixedLength(_) => panic!("duplicate protocol attribute `{}`", FIXED_LENGTH),
                _ => unreachable!()
            }
        } else {
            self.length = Some(length);
        }
    }
}

#[derive(Debug)]
pub enum Protocol {
    DiscriminantFormat(format::Enum),
    Discriminator(syn::Lit),
    LengthPrefix {
        kind: LengthPrefixKind,
        prefix_field_name: syn::Ident,
        prefix_subfield_names: Vec<syn::Ident>,
    },
    FixedLength(usize),
    FixedLengthPath(syn::Path),
    SkipIf(SkipExpression),
}

/// A skip condition, either path, binary expression or unary expression
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SkipExpression {
    PathExp(ExprPath),
    BinaryExp(ExprBinary),
    UnaryExp(ExprUnary),
    Path(syn::Path),
}

impl SkipExpression {
    pub fn parse_from(exp: &str) -> SkipExpression {
        let expr = syn::parse_str::<Expr>(exp).unwrap();

        match expr {
            Expr::Binary(e) => SkipExpression::BinaryExp(e),
            Expr::Unary(e) => SkipExpression::UnaryExp(e),
            Expr::Path(e) => SkipExpression::PathExp(e),
            _ => panic!("Unexpected skip expression")
        }
    }

    pub fn to_token_stream(&self) -> TokenStream {
        match self {
            SkipExpression::PathExp(e) => e.to_token_stream(),
            SkipExpression::BinaryExp(e) => e.to_token_stream(),
            SkipExpression::UnaryExp(e) => e.to_token_stream(),
            SkipExpression::Path(e) => e.to_token_stream(),
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum LengthPrefixKind {
    Bytes,
    Elements,
    Pointers,
}

impl LengthPrefixKind {
    /// Gets a path to the length prefix in the protocol crate.
    pub fn path_expr(&self) -> TokenStream {
        match *self {
            LengthPrefixKind::Bytes => quote!(djin_protocol::hint::LengthPrefixKind::Bytes),
            LengthPrefixKind::Elements => quote!(djin_protocol::hint::LengthPrefixKind::Elements),
            LengthPrefixKind::Pointers => quote!(djin_protocol::hint::LengthPrefixKind::Pointers)
        }
    }
}

/// Gets the value of the `repr(type)` attribute.
pub fn repr(attrs: &[syn::Attribute]) -> Option<syn::Ident> {
    attribute::with_ident(REPR, attrs)
}


pub fn protocol(attrs: &[syn::Attribute]) -> AttributeContainer {
    let meta_lists = attrs.iter().filter_map(|attr| match attr.parse_meta() {
        Ok(syn::Meta::List(meta_list)) => {
            if meta_list.path.get_ident() == Some(&syn::Ident::new("protocol", proc_macro2::Span::call_site())) {
                Some(meta_list)
            } else {
                // Unrelated attribute.
                None
            }
        }
        _ => None,
    }).collect::<Vec<MetaList>>();

    let mut attributes: AttributeContainer = AttributeContainer::default();
    meta_lists.into_iter().for_each(|meta_list| {
        meta_list.nested.into_iter().for_each(|nested_metas| {
            match nested_metas {
                NestedMeta::Meta(syn::Meta::List(nested_list)) => {
                    match &nested_list.path.get_ident().expect("meta is not an ident").to_string()[..] {
                        // #[protocol(length_prefix(<kind>(<prefix field name>)))]
                        SKIP_IF => parse_skip_attr(&mut attributes, &nested_list),
                        FIXED_LENGTH => parse_fixed_length_attr(&mut attributes, &nested_list),
                        LENGTH_PREFIX => parse_length_prefix_attr(&mut attributes, &nested_list),
                        DISCRIMINATOR => parse_discriminator_attr(&mut attributes, &nested_list),
                        name => panic!("#[protocol({})] is not valid", name),
                    }
                }
                NestedMeta::Meta(syn::Meta::NameValue(name_value)) => {
                    match name_value.path.get_ident() {
                        Some(ident) => {
                            match &ident.to_string()[..] {
                                // #[protocol(discriminant = "<format_name>")]
                                DISCRIMINANT => parse_discriminant_attr(&mut attributes, name_value),
                                ident => panic!("expected 'discriminant' but got '{}", ident),
                            }
                        }
                        None => panic!("expected 'discriminant' but the parsed string was not even an identifier"),
                    }
                }
                _ => panic!("#[protocol(..)] attributes cannot be empty"),
            }

        })
    });

    attributes
}

fn parse_discriminant_attr(attributes: &mut AttributeContainer, name_value: MetaNameValue) {
    let format_kind = match name_value.lit {
        syn::Lit::Str(s) => match format::Enum::from_str(&s.value()) {
            Ok(f) => f,
            Err(()) => panic!("invalid enum discriminant format: '{}", s.value()),
        },
        _ => panic!("discriminant format mut be string"),
    };

    attributes.set_discriminant(Protocol::DiscriminantFormat(format_kind));
}

fn parse_discriminator_attr(attributes: &mut AttributeContainer, nested_list: &MetaList) {

    let literal = expect::meta_list::single_literal(nested_list)
        .expect("expected a single literal");
    attributes.set_dicriminator(Protocol::Discriminator(literal));
}

fn  parse_length_prefix_attr(attributes: &mut AttributeContainer, nested_list: &MetaList) {
    let nested_list = expect::meta_list::nested_list(nested_list)
        .expect("expected a nested list");
    let prefix_kind = match &nested_list.path.get_ident().expect("nested list is not an ident").to_string()[..] {
        "bytes" => LengthPrefixKind::Bytes,
        "elements" => LengthPrefixKind::Elements,
        "pointers" => LengthPrefixKind::Pointers,
        invalid_prefix => panic!("invalid length prefix type: '{}'", invalid_prefix),
    };

    let length_prefix_expr = expect::meta_list::single_element(&nested_list).unwrap();
    let (prefix_field_name, prefix_subfield_names) = match length_prefix_expr {
        syn::NestedMeta::Lit(syn::Lit::Str(s)) => {
            let mut parts: Vec<_> = s.value()
                .split(".")
                .map(|s| syn::Ident::new(s, Span::call_site()))
                .collect();

            if parts.len() < 1 {
                panic!("there must be at least one field mentioned");
            }

            let field_ident = parts.remove(0);
            let subfield_idents = parts.into_iter().collect();

            (field_ident, subfield_idents)
        }
        syn::NestedMeta::Meta(syn::Meta::Path(path)) => match path.get_ident() {
            Some(field_ident) => (field_ident.clone(), Vec::new()),
            None => panic!("path is not an ident"),
        },
        _ => panic!("unexpected format for length prefix attribute"),
    };

    attributes.set_length(Protocol::LengthPrefix { kind:  prefix_kind, prefix_field_name, prefix_subfield_names });
}

fn parse_fixed_length_attr(attributes: &mut AttributeContainer, nested_list: &MetaList) {
    let nested_list = expect::meta_list::single_element(&nested_list).unwrap();


    match nested_list {
        syn::NestedMeta::Lit(syn::Lit::Int(len))  => {
            let len = len.base10_parse::<usize>().expect("Invalid fixed length, expected usize");
            attributes.set_length(Protocol::FixedLength(len));
        }
        syn::NestedMeta::Lit(syn::Lit::Str(lit))  => {
            let path: syn::Path = lit.parse().unwrap();
            attributes.set_length(Protocol::FixedLengthPath(path));
        }
        syn::NestedMeta::Meta(syn::Meta::Path(path)) =>  {
            attributes.set_length(Protocol::FixedLengthPath(path))
        }
        _ => panic!("Invalid fixed length, expected usize")
    }
}

fn parse_skip_attr(attributes: &mut AttributeContainer, nested_list: &MetaList) {
    let expression = expect::meta_list::single_element(nested_list).unwrap();
    let expression = match expression {
        syn::NestedMeta::Lit(syn::Lit::Str(s)) => {
            SkipExpression::parse_from(&s.value())
        }
        syn::NestedMeta::Meta(syn::Meta::Path(path)) => {
            SkipExpression::Path(path)
        }
        _ => panic!("Expected a path, binary or unary expression")
    };

    attributes.set_skip_if(Protocol::SkipIf(expression));
}

mod expect {
    pub mod meta_list {
        use syn::MetaList;

        pub fn nested_list(list: &MetaList) -> Result<MetaList, ()> {
            assert_eq!(list.nested.len(), 1, "list should only have one item");
            match list.nested.iter().next().unwrap() {
                syn::NestedMeta::Meta(syn::Meta::List(nested)) => Ok(nested.clone()),
                _ => Err(()),
            }
        }

        /// Expects a list with a single element.
        pub fn single_element(list: &MetaList) -> Result<syn::NestedMeta, ()> {
            assert_eq!(list.nested.len(), 1, "list should only have one item");
            Ok(list.nested.iter().next().unwrap().clone())
        }

        /// A single word `name(literal)`.
        pub fn single_literal(list: &MetaList)
                              -> Result<syn::Lit, ()> {
            single_element(list).and_then(|nested| match nested {
                syn::NestedMeta::Lit(lit) => Ok(lit),
                _ => Err(()),
            })
        }
    }
}

mod attribute {
    pub fn with_list(name: &str, attrs: &[syn::Attribute]) -> Option<Vec<syn::NestedMeta>> {
        attrs.iter().filter_map(|attr| match attr.parse_meta() {
            Ok(syn::Meta::List(list)) => {
                match list.path.get_ident() {
                    Some(ident) if ident == name => Some(list.nested.into_iter().collect()),
                    _ => None,
                }
            }
            _ => None,
        }).next()
    }

    pub fn with_unitary_list(name: &str, attrs: &[syn::Attribute]) -> Option<syn::NestedMeta> {
        with_list(name, attrs).map(|list| {
            if list.len() != 1 { panic!("expected only one meta inside list but found {}", list.len()); }
            list.into_iter().next().unwrap()
        })
    }

    pub fn with_ident(name: &str, attrs: &[syn::Attribute]) -> Option<syn::Ident> {
        with_unitary_list(name, attrs).map(|nested| match nested {
            syn::NestedMeta::Meta(syn::Meta::Path(path)) => match path.get_ident() {
                Some(ident) => ident.clone(),
                None => panic!("expected an ident"),
            },
            _ => panic!("expected an ident"),
        })
    }
}

#[cfg(test)]
mod test {
    use crate::attr::SkipExpression;

    #[test]
    fn should_parse_skip_expression() {
        let binary = "a == b";
        let parse_result = SkipExpression::parse_from(binary);
        assert!(matches!(parse_result, SkipExpression::BinaryExp(_)));

        let unary = "!b";
        let parse_result = SkipExpression::parse_from(unary);
        assert!(matches!(parse_result, SkipExpression::UnaryExp(_)));

        let path = "hello";
        let parse_result = SkipExpression::parse_from(path);
        assert!(matches!(parse_result, SkipExpression::PathExp(_)));
    }

    #[test]
    fn should_convert_expression_to_token() {
        let binary = "a == b";
        let parse_result = SkipExpression::parse_from(binary);
        let tokens = parse_result.to_token_stream();
        let expression = quote! { #tokens };
        assert_eq!(expression.to_string(), "a == b");
    }
}

