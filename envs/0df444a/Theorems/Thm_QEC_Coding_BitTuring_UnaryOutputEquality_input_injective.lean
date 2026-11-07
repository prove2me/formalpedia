-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryOutputEquality_input_injective
-- name    : QEC.Coding.BitTuring.UnaryOutputEquality.input_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:05:55.297645+00:00
-- url     : https://prove2.me/theorems/9500464d-9d1a-4f8d-b85a-7c0618c3a669
-- title:
--   Unary Output Equality: input injective
-- statement:
--   A faithful body encoding gives a faithful whole equality-trial input.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryOutputEquality.lean#L308-L313
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryOutputEquality.lean#L308-L313

import Definitions.Def_QEC_Coding_BitTuring_UnaryFactorTest
import Definitions.Def_QEC_Coding_BitTuring_UnaryOutputEquality
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryOutputEquality
open Turing StateTransition UnaryArithmetic
variable (A : Machine)

theorem QEC.Coding.BitTuring.UnaryOutputEquality.input_injective {α : Type} (encode : α→List Bool) (hi : Function.Injective encode) :
    Function.Injective (input encode) := by sorry
