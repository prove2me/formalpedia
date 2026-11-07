-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedForgetLevel_toSpecZ
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedForgetLevel_toSpecZ
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T04:00:25.909967+00:00
-- url     : https://prove2.me/theorems/13ac326b-bd7e-48cd-ab36-bbc6adc53061
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Glued Forget Level to Spec Z
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal Glued Forget Level to Spec Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerLevelMorphism.lean#L359-L366
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerLevelMorphism.lean#L359-L366

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalHeckePullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelMorphism
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedForgetLevel_toSpecZ
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    lpsOriginalIntegerNormalGluedForgetLevel N M hNM h4N hN hM ≫
      lpsOriginalIntegerNormalGluedToSpecZ N hN =
    lpsOriginalIntegerNormalGluedToSpecZ M hM := by sorry
