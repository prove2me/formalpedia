-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_Remainder_input_injective
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.Remainder.input_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:04:30.746388+00:00
-- url     : https://prove2.me/theorems/0ac0ac2c-b065-4300-88ad-8dddad5b4606
-- title:
--   Remainder: input injective
-- statement:
--   The actual pair encoding distinguishes every positive-modulus input.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryRemainder.lean#L297-L302
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryRemainder.lean#L297-L302

import Definitions.Def_QEC_Coding_BitTuring_UnaryMultiplication
import Mathlib.Data.ZMod.Basic
import Definitions.Def_QEC_Coding_BitTuring_UnaryRemainder
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.Remainder
open Turing StateTransition

theorem QEC.Coding.BitTuring.UnaryArithmetic.Remainder.input_injective : Function.Injective input := by sorry
