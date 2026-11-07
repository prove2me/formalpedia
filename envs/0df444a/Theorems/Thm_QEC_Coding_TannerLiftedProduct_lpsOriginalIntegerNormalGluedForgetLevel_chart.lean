-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedForgetLevel_chart
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedForgetLevel_chart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:13:57.884276+00:00
-- url     : https://prove2.me/theorems/adabd73b-3843-42b4-86eb-a2422d1b55ae
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Glued Forget Level chart
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal Glued Forget Level chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerLevelMorphism.lean#L264-L271
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerLevelMorphism.lean#L264-L271

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalHeckePullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelMorphism
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedForgetLevel_chart
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) (b : Bool) :
    lpsOriginalIntegerNormalGluedChartMap M hM b ≫
      lpsOriginalIntegerNormalGluedForgetLevel N M hNM h4N hN hM =
    lpsOriginalIntegerNormalSchemeLevelChartMap N M hNM h4N hN hM b ≫
      lpsOriginalIntegerNormalGluedChartMap N hN b := by sorry
