-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSOriginalGeneratorIndexMachine_result_decode
-- name    : QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.result_decode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:45:38.272249+00:00
-- url     : https://prove2.me/theorems/adf70e7a-426e-449a-80ef-5d285c38a128
-- title:
--   LPSOriginal Generator Index Machine: result decode
-- statement:
--   The original finite index decodes to the exact original quaternion group label.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGeneratorIndexMachine.lean#L380-L382
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGeneratorIndexMachine.lean#L380-L382

import Definitions.Def_QEC_Coding_BitTuring_UnaryRetainedFieldComputation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPSLIndexMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPSLLookupMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGeneratorMatrixListMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGeneratorIndexMachine
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine._p2m_local_instance_8252a2e3b6_378

theorem QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.result_decode {p:ℕ} (a:LPSResiduePrime p) (t:LPSGeneratorIndex p):
 (lpsPSLEnumerationEquiv a.q) (result a t)=lpsQuaternionLabel a t:= by sorry
