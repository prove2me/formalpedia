-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSOriginalGeneratorIndexMachine_output_length_lt_card
-- name    : QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.output_length_lt_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:57:36.540809+00:00
-- url     : https://prove2.me/theorems/8d5b04d0-f2f2-4c6b-8a86-4fcf21800687
-- title:
--   LPSOriginal Generator Index Machine: output length lt card
-- statement:
--   Original unary generator index length is below the genuine PSL cardinality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGeneratorIndexMachine.lean#L158-L162
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGeneratorIndexMachine.lean#L158-L162

import Definitions.Def_QEC_Coding_BitTuring_UnaryRetainedFieldComputation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPSLIndexMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPSLLookupMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGeneratorMatrixListMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGeneratorIndexMachine
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSOriginalPSLIndexMachine_output_length_lt_card

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open LPSPSLSearchMachine
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine._p2m_local_instance_8252a2e3b6_28

theorem QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.output_length_lt_card {p:ℕ} (a:LPSResiduePrime p) (t:LPSGeneratorIndex p):
 (output a t).length<Fintype.card PSL(2,ZMod a.q):= by sorry
