-- Prove2me | Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularDot_input_injective
-- name    : QEC.Coding.BitTuring.UnaryArithmetic.ModularDot.input_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:16:40.012063+00:00
-- url     : https://prove2.me/theorems/ff9ec1c2-398a-4a9e-9226-99c3a6b13750
-- title:
--   Modular Dot: input injective
-- statement:
--   The actual encoding distinguishes every domain input.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryModularDot.lean#L164-L175
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryModularDot.lean#L164-L175

import Definitions.Def_QEC_Coding_BitTuring_UnaryModularSum
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_BitTuring_UnaryModularProduct
import Definitions.Def_QEC_Coding_BitTuring_UnaryInverseInput
import Mathlib.Tactic.Linarith
import Definitions.Def_QEC_Coding_BitTuring_UnaryModularDot
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularProduct_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularSum_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_Remainder_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryOutputEquality_input_injective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.ModularDot
open Turing
open FieldProjection

theorem QEC.Coding.BitTuring.UnaryArithmetic.ModularDot.input_injective : Function.Injective input := by sorry
