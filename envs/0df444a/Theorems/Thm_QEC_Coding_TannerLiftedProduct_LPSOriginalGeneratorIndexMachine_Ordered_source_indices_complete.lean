-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSOriginalGeneratorIndexMachine_Ordered_source_indices_complete
-- name    : QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Ordered.source_indices_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:52:47.943872+00:00
-- url     : https://prove2.me/theorems/5c5678f9-e1c1-4ed6-bcdf-b1f8e4e25d55
-- title:
--   Ordered: source indices complete
-- statement:
--   Every original normalized source generator occurs in the computed ordered index list.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGeneratorIndexMachine.lean#L442-L445
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGeneratorIndexMachine.lean#L442-L445

import Definitions.Def_QEC_Coding_BitTuring_UnaryRetainedFieldComputation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPSLIndexMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPSLLookupMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGeneratorMatrixListMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGeneratorIndexMachine
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Ordered
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Ordered._p2m_local_instance_8252a2e3b6_393

theorem QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Ordered.source_indices_complete {p:ℕ} (a:LPSResiduePrime p) (t:LPSGeneratorIndex p):
 (result a t).val∈indices a (LPSGeneratorMatrixListMachine.sourceDirections a.degreePrime a.degreeModFour):= by sorry
