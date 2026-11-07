-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPSLIndexMul_decode
-- name    : QEC.Coding.TannerLiftedProduct.lpsPSLIndexMul_decode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:33:51.764756+00:00
-- url     : https://prove2.me/theorems/f574fa3f-0756-47f9-981c-b71ad602602e
-- title:
--   Tanner Lifted Product: lps PSLIndex Mul decode
-- statement:
--   The Tanner Lifted Product construction uses the lps PSLIndex Mul decode property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSVertexEnumeration.lean#L133-L137
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSVertexEnumeration.lean#L133-L137

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveNormalization
import Mathlib.Data.List.FinRange
import Mathlib.Data.Quot
import Mathlib.Data.List.NodupEquivFin
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSVertexEnumeration
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_747ca7d85c_18

theorem QEC.Coding.TannerLiftedProduct.lpsPSLIndexMul_decode (q : ℕ) [Fact q.Prime]
    (i j : Fin (lpsPSLList q).length) :
    (lpsPSLEnumerationEquiv q) (lpsPSLIndexMul q i j) =
      (lpsPSLEnumerationEquiv q) i * (lpsPSLEnumerationEquiv q) j := by sorry
