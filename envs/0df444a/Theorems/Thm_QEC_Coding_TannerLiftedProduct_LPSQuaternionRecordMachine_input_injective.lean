-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSQuaternionRecordMachine_input_injective
-- name    : QEC.Coding.TannerLiftedProduct.LPSQuaternionRecordMachine.input_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:01:59.227172+00:00
-- url     : https://prove2.me/theorems/f7aa4a26-6564-4a55-bf08-d434549da3aa
-- title:
--   LPSQuaternion Record Machine: input injective
-- statement:
--   Source input encoding remains faithful to the growing original family member.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionRecordMachine.lean#L240-L241
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionRecordMachine.lean#L240-L241

import Definitions.Def_QEC_Coding_BitTuring_UnarySignedCoefficient
import Definitions.Def_QEC_Coding_BitTuring_ModulusQuery
import Definitions.Def_QEC_Coding_BitTuring_BitDelimiters
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSInverseMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSMatrixProductMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionRecordMachine
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularDot_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularInverse_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularMatrixProduct_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularNegation_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularProduct_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularSum_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ProductSearch_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_Remainder_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_SignedCoefficient_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_SquareRoot_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryOutputEquality_input_injective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSQuaternionRecordMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition
open FieldProjection
open scoped MatrixGroups

theorem QEC.Coding.TannerLiftedProduct.LPSQuaternionRecordMachine.input_injective (p:ℕ) : Function.Injective (fun a:LPSResiduePrime p=>unary a.q) := by sorry
