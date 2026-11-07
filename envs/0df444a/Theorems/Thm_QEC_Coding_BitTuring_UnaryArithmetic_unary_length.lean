-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_unary_length
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.unary_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:03:50.062705+00:00
-- url     : https://prove2.me/theorems/cf96129d-ca46-4c93-b8ab-21407f76abb4
-- title:
--   Unary Arithmetic: unary length
-- statement:
--   The actual unary bit-string length is the encoded natural value.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryMultiplication.lean#L159-L159
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryMultiplication.lean#L159-L159

import Definitions.Def_QEC_Coding_BitTuring_Composition
import Definitions.Def_QEC_Coding_BitTuring_UnaryMultiplication
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open Turing StateTransition

theorem QEC.Coding.BitTuring.UnaryArithmetic.unary_length (n : ℕ) : (unary n).length = n := by sorry
