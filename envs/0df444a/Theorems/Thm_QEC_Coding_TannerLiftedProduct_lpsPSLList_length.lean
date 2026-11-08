-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPSLList_length
-- name    : QEC.Coding.TannerLiftedProduct.lpsPSLList_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:55:09.319475+00:00
-- url     : https://prove2.me/theorems/c67e4b89-2e23-4580-acdc-e30bbc60c164
-- title:
--   Tanner Lifted Product: lps PSLList length
-- statement:
--   The Tanner Lifted Product construction uses the lps PSLList length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSVertexEnumeration.lean#L116-L119
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSVertexEnumeration.lean#L116-L119

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveNormalization
import Mathlib.Data.List.FinRange
import Mathlib.Data.Quot
import Mathlib.Data.List.NodupEquivFin
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSVertexEnumeration
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_747ca7d85c_18

theorem QEC.Coding.TannerLiftedProduct.lpsPSLList_length (q : ℕ) [Fact q.Prime] (hqTwo : q ≠ 2) :
    (lpsPSLList q).length = q * (q ^ 2 - 1) / 2 := by sorry
