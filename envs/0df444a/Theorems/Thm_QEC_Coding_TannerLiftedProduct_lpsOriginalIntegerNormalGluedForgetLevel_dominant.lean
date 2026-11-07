-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedForgetLevel_dominant
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedForgetLevel_dominant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:11:54.081715+00:00
-- url     : https://prove2.me/theorems/04a28b11-da12-4ef5-9228-618d9e03f523
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Glued Forget Level dominant
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal Glued Forget Level dominant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerLevelFunctionField.lean#L110-L126
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerLevelFunctionField.lean#L110-L126

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelMorphism
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelFunctionField
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedForgetLevel_dominant
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    IsDominant (lpsOriginalIntegerNormalGluedForgetLevel N M hNM h4N hN hM) := by sorry
