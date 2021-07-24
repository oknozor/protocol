use djin_protocol::{Parcel, Settings};


#[derive(Protocol, Debug, PartialEq, Eq)]
struct WithLengthPrefixSeparateType {
    pub prefix: Prefix,
    #[protocol(length_prefix(bytes("prefix.reason_length")))]
    pub reason: String,
}

#[derive(Protocol, Debug, PartialEq, Eq)]
struct Foo<L: Parcel> {
    pub reason_length: u16,
    pub other: u8,
    #[protocol(length_prefix(bytes(reason_length)))]
    pub reason: L,
}

#[derive(Protocol, Debug, PartialEq, Eq)]
pub struct Prefix {
    pub reason_length: u8,
}

#[derive(Protocol, Debug, PartialEq, Eq)]
pub struct WithElementsLength {
    pub count: u32,
    pub foo: bool,
    #[protocol(length_prefix(elements(count)))]
    pub data: Vec<u32>,
}

#[derive(Protocol, Debug, PartialEq, Eq)]
pub struct WithTwoPrefix {
    pub count: u32,
    pub count_2: u32,
    pub foo: bool,
    #[protocol(length_prefix(elements(count)))]
    pub data: Vec<u32>,
    #[protocol(length_prefix(elements(count_2)))]
    pub data_2: Vec<u32>,
}

#[derive(Protocol, Debug, PartialEq, Eq)]
pub struct WithElementsLengthUsedTwice {
    pub count: u32,
    pub foo: bool,
    #[protocol(length_prefix(elements(count)))]
    pub data_1: Vec<u32>,
    #[protocol(length_prefix(elements(count)))]
    pub data_2: Vec<u32>,
}

#[derive(Protocol, Debug, PartialEq, Eq)]
pub struct WithFixedLength {
    #[protocol(fixed_length(3))]
    pub data: Vec<u32>,
}

const LENGTH: usize = 3;

#[derive(Protocol, Debug, PartialEq, Eq)]
pub struct FixedLengthWithPathStr {
    #[protocol(fixed_length("LENGTH"))]
    pub data: Vec<u32>,
}

#[derive(Protocol, Debug, PartialEq, Eq)]
pub struct FixedLengthWithPath {
    #[protocol(fixed_length(LENGTH))]
    pub data: Vec<u32>,
}


#[derive(Protocol, Debug, PartialEq, Eq)]
pub struct PointerLength {
    #[protocol(fixed_length(3))]
    pub ptr: Vec<u32>,
    #[protocol(length_prefix(pointers(ptr)))]
    pub data: Vec<u32>,
}


#[test]
fn can_read_length_prefix_5_bytes_string() {
    assert_eq!(Foo {
        reason_length: 5,
        other: 123,
        reason: "hello".to_owned(),
    }, Foo::from_raw_bytes(&[0, 5, 123, b'h', b'e', b'l', b'l', b'o'], &Settings::default()).unwrap());
}

#[test]
fn can_read_length_prefix_8_bytes_u32_array() {
    assert_eq!(Foo {
        reason_length: 8,
        other: 123,
        reason: vec![0x00ff00ff, 0x00ff00ff],
    }, Foo::from_raw_bytes(&[0, 8, 123, 0, !0, 0, !0, 0, !0, 0, !0], &Settings::default()).unwrap());
}


#[test]
fn can_read_length_prefix_3_elements() {
    assert_eq!(WithElementsLength {
        count: 3,
        foo: true,
        data: vec![1, 2, 3],
    }, WithElementsLength::from_raw_bytes(
                           &[0, 0, 0, 3, // disjoint length prefix
                             1, // boolean true
                             0, 0, 0, 1, // 1
                             0, 0, 0, 2, // 2
                             0, 0, 0, 3], // 3
                             &Settings::default()).unwrap());
}

#[test]
fn can_read_twice_the_same_prefix_length() {
    assert_eq!(WithElementsLengthUsedTwice {
        count: 3,
        foo: true,
        data_1: vec![1, 2, 3],
        data_2: vec![4, 5, 6],
    }, WithElementsLengthUsedTwice::from_raw_bytes(
        &[0, 0, 0, 3, // disjoint length prefix
            1, // boolean true
            0, 0, 0, 1, // 1
            0, 0, 0, 2, // 2
            0, 0, 0, 3, // 3
            0, 0, 0, 4, // 4
            0, 0, 0, 5, // 5
            0, 0, 0, 6  // 6
        ],
        &Settings::default()).unwrap());
}

#[test]
fn can_read_two_prefix_length() {
    assert_eq!(WithTwoPrefix {
        count: 3,
        count_2: 3,
        foo: true,
        data: vec![1, 2, 3],
        data_2: vec![4, 5, 6],
    }, WithTwoPrefix::from_raw_bytes(
        &[
            0, 0, 0, 3, // disjoint length prefix
            0, 0, 0, 3, // disjoint length prefix
            1, // boolean true
            0, 0, 0, 1, // 1
            0, 0, 0, 2, // 2
            0, 0, 0, 3, // 3
            0, 0, 0, 4, // 4
            0, 0, 0, 5, // 5
            0, 0, 0, 6  // 6
        ],
        &Settings::default()).unwrap());
}

#[test]
fn can_read_fixed_length_prefix() {

    assert_eq!(WithFixedLength {
        data: vec![1, 2, 3],
    }, WithFixedLength::from_raw_bytes(
        &[
            0, 0, 0, 1, // 1
            0, 0, 0, 2, // 2
            0, 0, 0, 3  // 3
        ],
        &Settings::default()).unwrap());
}

#[test]
fn can_read_pointer_length_prefix() {
    assert_eq!(PointerLength {
        ptr: vec![0, 0, 1],
        data: vec![3],
    }, PointerLength::from_raw_bytes(
        &[
            0, 0, 0, 0,// Disabled
            0, 0, 0, 0,// Disabled
            0, 0, 0, 1,// Enabled
            0, 0, 0, 3 // element enabled 1
        ],
        &Settings::default()).unwrap());
}

#[test]
fn can_read_pointer_length_prefix_2() {
    assert_eq!(PointerLength {
        ptr: vec![0, 2, 1],
        data: vec![3, 6],
    }, PointerLength::from_raw_bytes(
        &[
            0, 0, 0, 0, // Disabled
            0, 0, 0, 2, // Enabled
            0, 0, 0, 1, // Enabled
            0, 0, 0, 3, // element enabled 1
            0, 0, 0, 6  // element enabled 1
        ], &Settings::default()).unwrap());
}

#[test]
fn read_fixed_length_with_path() {

    assert_eq!(FixedLengthWithPath {
        data: vec![1, 2, 3],
    }, FixedLengthWithPath::from_raw_bytes(
        &[
            0, 0, 0, 1, // 1
            0, 0, 0, 2, // 2
            0, 0, 0, 3,  // 3
            0, 0, 0, 3,  // 3
        ],
        &Settings::default()).unwrap());
}


