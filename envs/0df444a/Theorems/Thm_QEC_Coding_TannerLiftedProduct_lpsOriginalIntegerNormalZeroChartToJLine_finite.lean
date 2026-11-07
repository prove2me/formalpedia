-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalZeroChartToJLine_finite
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalZeroChartToJLine_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:59:00.247302+00:00
-- url     : https://prove2.me/theorems/9fade6d9-23b7-485b-8e45-5004291c20ad
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Zero Chart To JLine finite
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal Zero Chart To JLine finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerProperModel.lean#L226-L235
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerProperModel.lean#L226-L235

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalZeroChartToJLine_finite
    (N : ℕ) [NeZero N] (hN : 0<N) :
    IsFinite (lpsOriginalIntegerNormalZeroChartToJLine N hN) := by sorry
