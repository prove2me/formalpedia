-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalChartProjection_comp
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalChartProjection_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:56:29.410055+00:00
-- url     : https://prove2.me/theorems/6a98547e-84d8-41f6-810c-42ca21c13a0f
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Chart Projection comp
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal Chart Projection comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerProperModel.lean#L737-L742
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerProperModel.lean#L737-L742

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelCharts
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.OpenImmersion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalChartProjection_comp
    (N : ℕ) (hN : 0<N) (b : Bool) :
    lpsOriginalIntegerNormalChartProjection N hN b ≫
      lpsOriginalIntegerProjectiveJChartMap b =
    lpsOriginalIntegerNormalChartToProjectiveJ N hN b := by sorry
