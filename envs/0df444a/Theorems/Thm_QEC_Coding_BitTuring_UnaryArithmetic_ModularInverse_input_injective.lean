-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularInverse_input_injective
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.ModularInverse.input_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:31:07.864576+00:00
-- url     : https://prove2.me/theorems/387e2695-2a75-466e-aee5-3dd4641ff953
-- title:
--   Modular Inverse: input injective
-- statement:
--   The actual input distinguishes every non-proof domain parameter.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFieldInverse.lean#L84-L86
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFieldInverse.lean#L84-L86

import Definitions.Def_QEC_Coding_BitTuring_UnaryProductSearch
import Definitions.Def_QEC_Coding_BitTuring_UnaryInverseInput
import Mathlib.Algebra.Field.ZMod
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldInverse
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularProduct_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ProductSearch_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_Remainder_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_SquareRoot_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryOutputEquality_input_injective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.ModularInverse
open Turing StateTransition

theorem QEC.Coding.BitTuring.UnaryArithmetic.ModularInverse.input_injective : Function.Injective input := by sorry
