-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPSLIndexInv_decode
-- name    : QEC.Coding.TannerLiftedProduct.lpsPSLIndexInv_decode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:33:51.860043+00:00
-- url     : https://prove2.me/theorems/7365ec39-bf7d-4f15-b357-90b0a5b08799
-- title:
--   Tanner Lifted Product: lps PSLIndex Inv decode
-- statement:
--   The Tanner Lifted Product construction uses the lps PSLIndex Inv decode property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSVertexEnumeration.lean#L139-L143
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSVertexEnumeration.lean#L139-L143

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveNormalization
import Mathlib.Data.List.FinRange
import Mathlib.Data.Quot
import Mathlib.Data.List.NodupEquivFin
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSVertexEnumeration
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_747ca7d85c_18

theorem QEC.Coding.TannerLiftedProduct.lpsPSLIndexInv_decode (q : ℕ) [Fact q.Prime]
    (i : Fin (lpsPSLList q).length) :
    (lpsPSLEnumerationEquiv q) (lpsPSLIndexInv q i) =
      ((lpsPSLEnumerationEquiv q) i)⁻¹ := by sorry
