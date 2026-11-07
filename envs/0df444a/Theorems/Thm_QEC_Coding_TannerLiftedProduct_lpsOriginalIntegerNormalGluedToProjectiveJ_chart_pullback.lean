-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedToProjectiveJ_chart_pullback
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedToProjectiveJ_chart_pullback
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:01:23.370502+00:00
-- url     : https://prove2.me/theorems/68276664-4c93-4748-9cf9-7ac46de2905b
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Glued To Projective J chart pullback
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal Glued To Projective J chart pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerProperModel.lean#L760-L790
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerProperModel.lean#L760-L790

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedToProjectiveJ_chart_pullback
    (N : ℕ) (hN : 0<N) (b : Bool) :
    IsPullback (lpsOriginalIntegerNormalGluedChartMap N hN b)
      (lpsOriginalIntegerNormalChartProjection N hN b)
      (lpsOriginalIntegerNormalGluedToProjectiveJ N hN)
      (lpsOriginalIntegerProjectiveJChartMap b) := by sorry
