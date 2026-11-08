-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSSLInverseMachine_input_injective
-- name    : QEC.Coding.TannerLiftedProduct.LPSSLInverseMachine.input_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:31:52.177974+00:00
-- url     : https://prove2.me/theorems/36f82df0-0f87-4b55-9af4-babac3fe34dc
-- title:
--   LPSSLInverse Machine: input injective
-- statement:
--   The source encoding distinguishes every original SL matrix at a positive modulus.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSLInverseMachine.lean#L91-L95
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSLInverseMachine.lean#L91-L95

import Definitions.Def_QEC_Coding_BitTuring_UnaryModularAdjugate
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSMatrixProductMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSLInverseMachine
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularAdjugate_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularDot_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularInverse_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularMatrixProduct_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularNegation_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularProduct_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularSum_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ProductSearch_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_Remainder_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_SquareRoot_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryOutputEquality_input_injective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSSLInverseMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open Turing
open scoped MatrixGroups

theorem QEC.Coding.TannerLiftedProduct.LPSSLInverseMachine.input_injective (q:ℕ) (hq:0<q) : Function.Injective (input q) := by sorry
