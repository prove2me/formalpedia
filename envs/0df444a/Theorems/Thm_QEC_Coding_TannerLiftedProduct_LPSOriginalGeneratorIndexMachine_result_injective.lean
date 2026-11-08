-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSOriginalGeneratorIndexMachine_result_injective
-- name    : QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.result_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:45:24.063163+00:00
-- url     : https://prove2.me/theorems/2806fc41-61c3-4819-8dc2-7935627216d9
-- title:
--   LPSOriginal Generator Index Machine: result injective
-- statement:
--   Distinct original quaternion directions have distinct original finite vertex indices.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGeneratorIndexMachine.lean#L384-L388
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGeneratorIndexMachine.lean#L384-L388

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

theorem QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.result_injective {p:ℕ} (a:LPSResiduePrime p):Function.Injective (result a):= by sorry
