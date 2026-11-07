-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalChartProjection_finite
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalChartProjection_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:01:13.813198+00:00
-- url     : https://prove2.me/theorems/a204b56d-29c0-4f02-9c8c-00094aa9db87
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Chart Projection finite
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal Chart Projection finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerProperModel.lean#L744-L749
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerProperModel.lean#L744-L749

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalChartProjection_finite
    (N : ℕ) [NeZero N] (hN : 0<N) (b : Bool) :
    IsFinite (lpsOriginalIntegerNormalChartProjection N hN b) := by sorry
