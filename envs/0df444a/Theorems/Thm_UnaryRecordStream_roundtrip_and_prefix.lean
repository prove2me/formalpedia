-- Prove2me | Theorems.Thm_UnaryRecordStream_roundtrip_and_prefix
-- name    : UnaryRecordStream.roundtrip_and_prefix
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T21:15:17.98506+00:00
-- url     : https://prove2.me/theorems/f4649b3f-c7c6-541d-ac3a-9b64a9266794
-- title:
--   Exact decoding and prefix persistence for unary-delimited streams
-- statement:
--   Parse a finite stream by counting positive symbols until a zero completes each unary field. The canonical encoding uses n ones followed by zero to represent n. Every finite list of natural numbers decodes exactly after canonical encoding, that encoding uses only zero and one, and appending symbols to any input preserves the list of previously completed fields as a prefix of the newly decoded list.
-- source:
--   Direct induction on the unary code and the parser's accumulator.

import Definitions.Def_UnaryRecordStream

open UnaryRecordStream

theorem UnaryRecordStream.roundtrip_and_prefix :
    (∀ values, fields (encode values) = values) ∧
    (∀ left right, fields left <+: fields (left ++ right)) ∧
    (∀ values x, x ∈ encode values → x = 0 ∨ x = 1) := by sorry
