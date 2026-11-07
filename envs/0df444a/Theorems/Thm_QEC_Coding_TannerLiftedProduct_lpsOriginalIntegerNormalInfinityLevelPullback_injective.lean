-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalInfinityLevelPullback_injective
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalInfinityLevelPullback_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:16:40.556679+00:00
-- url     : https://prove2.me/theorems/8264cb5e-cc57-4ad0-8901-38690a7d1588
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Infinity Level Pullback injective
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal Infinity Level Pullback injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerLevelMorphism.lean#L381-L391
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerLevelMorphism.lean#L381-L391

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalHeckePullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelMorphism
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalInfinityLevelPullback_injective
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    Function.Injective (lpsOriginalIntegerNormalInfinityLevelPullback N M hNM h4N hN hM) := by sorry
