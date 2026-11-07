-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalZeroLevelPullback_injective
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalZeroLevelPullback_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:15:58.546376+00:00
-- url     : https://prove2.me/theorems/220c66fe-f0b3-4637-80b8-ef63b0987916
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Zero Level Pullback injective
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal Zero Level Pullback injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerLevelMorphism.lean#L369-L379
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerLevelMorphism.lean#L369-L379

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalHeckePullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelMorphism
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalZeroLevelPullback_injective
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    Function.Injective (lpsOriginalIntegerNormalZeroLevelPullback N M hNM h4N hN hM) := by sorry
