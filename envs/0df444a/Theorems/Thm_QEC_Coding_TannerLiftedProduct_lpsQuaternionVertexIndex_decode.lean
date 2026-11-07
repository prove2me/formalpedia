-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternionVertexIndex_decode
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuaternionVertexIndex_decode
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T01:55:23.502105+00:00
-- url     : https://prove2.me/theorems/10aad105-665e-4f86-b74e-bd4105020fc9
-- title:
--   Tanner Lifted Product: lps Quaternion Vertex Index decode
-- statement:
--   The Tanner Lifted Product construction uses the lps Quaternion Vertex Index decode property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSVertexEnumeration.lean#L149-L153
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSVertexEnumeration.lean#L149-L153

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveNormalization
import Mathlib.Data.List.FinRange
import Mathlib.Data.Quot
import Mathlib.Data.List.NodupEquivFin
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSVertexEnumeration
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_747ca7d85c_18

theorem QEC.Coding.TannerLiftedProduct.lpsQuaternionVertexIndex_decode {p : ℕ} (a : LPSResiduePrime p)
    (t : LPSQuaternion) (ht : t.norm = p) :
    (lpsPSLEnumerationEquiv a.q) (lpsQuaternionVertexIndex a t ht) =
      lpsQuaternionPSL a t ht := by sorry
