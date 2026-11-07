-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalSchemeLevelChartMap_toJ
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalSchemeLevelChartMap_toJ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:16:59.360762+00:00
-- url     : https://prove2.me/theorems/2d66d224-6900-4862-a5db-b8bd5172e635
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Scheme Level Chart Map to J
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal Scheme Level Chart Map to J property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerLevelMorphism.lean#L274-L325
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerLevelMorphism.lean#L274-L325

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalHeckePullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelMorphism
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalSchemeLevelChartMap_toJ
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) (b : Bool) :
    lpsOriginalIntegerNormalSchemeLevelChartMap N M hNM h4N hN hM b ≫
      lpsOriginalIntegerNormalChartToProjectiveJ N hN b =
    lpsOriginalIntegerNormalChartToProjectiveJ M hM b := by sorry
