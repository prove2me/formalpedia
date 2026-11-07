-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedToProjectiveJ_chart_apply
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedToProjectiveJ_chart_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:57:24.8625+00:00
-- url     : https://prove2.me/theorems/cf8b3896-661e-42fb-b1fd-b85db73e16fa
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Glued To Projective J chart apply
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal Glued To Projective J chart apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerProperModel.lean#L644-L652
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerProperModel.lean#L644-L652

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedToProjectiveJ_chart_apply
    (N : ℕ) (hN : 0<N) (b : Bool)
    (y : lpsOriginalIntegerNormalSchemeChart N hN b) :
    lpsOriginalIntegerNormalGluedToProjectiveJ N hN
      (lpsOriginalIntegerNormalGluedChartMap N hN b y) =
      lpsOriginalIntegerNormalChartToProjectiveJ N hN b y := by sorry
