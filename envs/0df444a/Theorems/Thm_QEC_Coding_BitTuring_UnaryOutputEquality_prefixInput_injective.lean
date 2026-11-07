-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryOutputEquality_prefixInput_injective
-- name    : QEC.Coding.BitTuring.UnaryOutputEquality.prefixInput_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:06:08.494201+00:00
-- url     : https://prove2.me/theorems/27e60fb1-a83f-4dfd-9743-8112e2f8e2c1
-- title:
--   Unary Output Equality: prefix Input injective
-- statement:
--   The prefix input distinguishes every natural target and encoded payload.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryOutputEquality.lean#L294-L301
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryOutputEquality.lean#L294-L301

import Definitions.Def_QEC_Coding_BitTuring_UnaryFactorTest
import Definitions.Def_QEC_Coding_BitTuring_UnaryOutputEquality
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryOutputEquality
open Turing StateTransition UnaryArithmetic
variable (A : Machine)

theorem QEC.Coding.BitTuring.UnaryOutputEquality.prefixInput_injective :
    Function.Injective (fun z:ℕ×List Bool => prefixInput z.1 z.2) := by sorry
