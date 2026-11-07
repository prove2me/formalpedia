-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalInfinityLevelPullback_coe
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalInfinityLevelPullback_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:16:59.66066+00:00
-- url     : https://prove2.me/theorems/27ec5bb9-aee8-45d7-939c-b39e6ae51727
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Infinity Level Pullback coe
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal Infinity Level Pullback coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerLevelMorphism.lean#L103-L112
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerLevelMorphism.lean#L103-L112

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalHeckePullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelMorphism
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalInfinityLevelPullback_coe
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) (x : lpsOriginalIntegerNormalInfinityChart N hN) :
    (((lpsOriginalIntegerNormalInfinityLevelPullback N M hNM h4N hN hM x :
      lpsOriginalIntegerNormalInfinityChart M hM) :
      lpsOriginalGeneratedFunctionFieldQ M hM) : LPSOriginalHolomorphicFractionField) =
      ((x : lpsOriginalGeneratedFunctionFieldQ N hN) :
        LPSOriginalHolomorphicFractionField) := by sorry
