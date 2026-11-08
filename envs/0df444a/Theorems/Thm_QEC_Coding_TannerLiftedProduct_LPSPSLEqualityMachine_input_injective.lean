-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSPSLEqualityMachine_input_injective
-- name    : QEC.Coding.TannerLiftedProduct.LPSPSLEqualityMachine.input_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:02:28.673214+00:00
-- url     : https://prove2.me/theorems/07c3a3fc-fad7-4e8b-8ed9-a6f4e5e8db63
-- title:
--   LPSPSLEquality Machine: input injective
-- statement:
--   Actual finite instructions or proved execution invariant, whole budget or original source certificate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSPSLEqualityMachine.lean#L66-L75
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSPSLEqualityMachine.lean#L66-L75

import Definitions.Def_QEC_Coding_BitTuring_UnaryPSLComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSMatrixProductMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPSLEqualityMachine
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularAdjugate_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularDot_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularInverse_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularMatrixProduct_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularNegation_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularProduct_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularSum_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_PSLComparison_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ProductSearch_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_Remainder_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_SquareRoot_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryOutputEquality_input_injective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSPSLEqualityMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open QEC.Coding.TannerLiftedProduct Turing StateTransition FieldProjection
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSPSLEqualityMachine._p2m_local_instance_54787d7fc4_22

theorem QEC.Coding.TannerLiftedProduct.LPSPSLEqualityMachine.input_injective (q:ℕ) (hq:0<q) : Function.Injective (fun x:SL(2,ZMod q)×SL(2,ZMod q)=>input q x.1 x.2) := by sorry
