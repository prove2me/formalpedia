-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalLevelFunctionFieldPullback_injective
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalLevelFunctionFieldPullback_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:13:46.798027+00:00
-- url     : https://prove2.me/theorems/db1d74da-98f1-4b67-820e-593b406f3b99
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Level Function Field Pullback injective
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal Level Function Field Pullback injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerLevelFunctionField.lean#L99-L108
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerLevelFunctionField.lean#L99-L108

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelMorphism
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelFunctionField
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalLevelFunctionFieldPullback_injective
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    letI := lpsOriginalIntegerNormalGluedScheme_integral N hN
    letI := lpsOriginalIntegerNormalGluedScheme_integral M hM
    Function.Injective (lpsOriginalIntegerNormalLevelFunctionFieldPullback
      N M hNM h4N hN hM) := by sorry
