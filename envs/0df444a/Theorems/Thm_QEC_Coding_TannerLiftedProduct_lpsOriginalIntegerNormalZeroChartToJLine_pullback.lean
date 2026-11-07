-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalZeroChartToJLine_pullback
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalZeroChartToJLine_pullback
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:00:29.658014+00:00
-- url     : https://prove2.me/theorems/21951070-88e3-491b-8e7f-12be7ca4dc42
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Zero Chart To JLine pullback
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal Zero Chart To JLine pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerProperModel.lean#L523-L560
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerProperModel.lean#L523-L560

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalZeroChartToJLine_pullback
    (N : ℕ) (hN : 0<N) :
    IsPullback (Spec.map (CommRingCat.ofHom (lpsOriginalIntegerNormalZeroToLaurent N hN)))
      (lpsOriginalIntegerNormalLaurentChartToJOverlap N hN)
      (lpsOriginalIntegerNormalZeroChartToJLine N hN)
      (lpsOriginalIntegerProjectiveJOverlapMap false) := by sorry
