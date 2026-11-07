-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalLevelInclusion_coe
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRationalLevelInclusion_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:12:21.690412+00:00
-- url     : https://prove2.me/theorems/bdd5e047-39c0-4f42-ab56-0fc2b3a602bb
-- title:
--   Tanner Lifted Product: lps Original Rational Level Inclusion coe
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Rational Level Inclusion coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerLevelMorphism.lean#L40-L48
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerLevelMorphism.lean#L40-L48

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalHeckePullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelMorphism
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRationalLevelInclusion_coe
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) (x : lpsOriginalGeneratedFunctionFieldQ N hN) :
    ((lpsOriginalRationalLevelInclusion N M hNM h4N hN hM x :
      lpsOriginalGeneratedFunctionFieldQ M hM) : LPSOriginalHolomorphicFractionField) =
      (x : LPSOriginalHolomorphicFractionField) := by sorry
