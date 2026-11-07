-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedForgetLevel_finite
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedForgetLevel_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:16:17.029894+00:00
-- url     : https://prove2.me/theorems/c204f3fe-9668-4f8c-afc8-62fc4483399d
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Glued Forget Level finite
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal Glued Forget Level finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerLevelMorphism.lean#L346-L357
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerLevelMorphism.lean#L346-L357

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalHeckePullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelMorphism
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedForgetLevel_finite
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    IsFinite (lpsOriginalIntegerNormalGluedForgetLevel N M hNM h4N hN hM) := by sorry
