-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedForgetLevel_toJ
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedForgetLevel_toJ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:13:25.285391+00:00
-- url     : https://prove2.me/theorems/54aa8191-3fd1-4eaf-9293-b3b3423f7e68
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Glued Forget Level to J
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal Glued Forget Level to J property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerLevelMorphism.lean#L327-L344
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerLevelMorphism.lean#L327-L344

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalHeckePullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelMorphism
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedForgetLevel_toJ
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    lpsOriginalIntegerNormalGluedForgetLevel N M hNM h4N hN hM ≫
      lpsOriginalIntegerNormalGluedToProjectiveJ N hN =
    lpsOriginalIntegerNormalGluedToProjectiveJ M hM := by sorry
