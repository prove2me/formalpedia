-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSOriginalPSLLookupMachine_original_index_roundtrip
-- name    : QEC.Coding.TannerLiftedProduct.LPSOriginalPSLLookupMachine.original_index_roundtrip
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:50:32.51706+00:00
-- url     : https://prove2.me/theorems/9765ded5-355c-4ec9-b09e-79e6c808ef4f
-- title:
--   LPSOriginal PSLLookup Machine: original index roundtrip
-- statement:
--   The merged original index function returns the supplied finite position.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPSLLookupMachine.lean#L220-L222
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPSLLookupMachine.lean#L220-L222

import Definitions.Def_QEC_Coding_BitTuring_UnaryFourFieldLookup
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPSLIndexMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPSLLookupMachine
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSOriginalPSLLookupMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalPSLLookupMachine._p2m_local_instance_eed6317f64_203

theorem QEC.Coding.TannerLiftedProduct.LPSOriginalPSLLookupMachine.original_index_roundtrip (q:ℕ) [Fact q.Prime] (i:Fin (lpsPSLList q).length):
 LPSOriginalPSLIndexMachine.rowIndex q (representative q i) (originalReps q)=i.val:= by sorry
