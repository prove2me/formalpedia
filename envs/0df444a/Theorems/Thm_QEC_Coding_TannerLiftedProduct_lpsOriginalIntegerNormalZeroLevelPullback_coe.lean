-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalZeroLevelPullback_coe
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalZeroLevelPullback_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:16:29.215591+00:00
-- url     : https://prove2.me/theorems/22a932f2-18f3-489f-b18a-95da206920ea
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Zero Level Pullback coe
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal Zero Level Pullback coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerLevelMorphism.lean#L92-L101
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerLevelMorphism.lean#L92-L101

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalHeckePullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelMorphism
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalZeroLevelPullback_coe
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) (x : lpsOriginalIntegerNormalZeroChart N hN) :
    (((lpsOriginalIntegerNormalZeroLevelPullback N M hNM h4N hN hM x :
      lpsOriginalIntegerNormalZeroChart M hM) :
      lpsOriginalGeneratedFunctionFieldQ M hM) : LPSOriginalHolomorphicFractionField) =
      ((x : lpsOriginalGeneratedFunctionFieldQ N hN) :
        LPSOriginalHolomorphicFractionField) := by sorry
