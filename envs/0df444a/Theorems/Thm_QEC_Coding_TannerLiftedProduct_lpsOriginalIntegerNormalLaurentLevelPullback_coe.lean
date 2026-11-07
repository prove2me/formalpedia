-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalLaurentLevelPullback_coe
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalLaurentLevelPullback_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:16:37.602276+00:00
-- url     : https://prove2.me/theorems/a97cc15a-5d4f-4e30-bd87-e208514fb577
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Laurent Level Pullback coe
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal Laurent Level Pullback coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerLevelMorphism.lean#L114-L123
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerLevelMorphism.lean#L114-L123

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalHeckePullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelMorphism
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalLaurentLevelPullback_coe
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) (x : lpsOriginalIntegerNormalLaurentChart N hN) :
    (((lpsOriginalIntegerNormalLaurentLevelPullback N M hNM h4N hN hM x :
      lpsOriginalIntegerNormalLaurentChart M hM) :
      lpsOriginalGeneratedFunctionFieldQ M hM) : LPSOriginalHolomorphicFractionField) =
      ((x : lpsOriginalGeneratedFunctionFieldQ N hN) :
        LPSOriginalHolomorphicFractionField) := by sorry
