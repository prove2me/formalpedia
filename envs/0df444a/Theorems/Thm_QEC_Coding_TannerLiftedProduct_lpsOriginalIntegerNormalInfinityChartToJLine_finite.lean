-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalInfinityChartToJLine_finite
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalInfinityChartToJLine_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:58:36.034671+00:00
-- url     : https://prove2.me/theorems/af7d6eb0-6ac7-4107-9deb-ad2980d9391c
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Infinity Chart To JLine finite
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal Infinity Chart To JLine finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerProperModel.lean#L237-L247
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerProperModel.lean#L237-L247

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalInfinityChartToJLine_finite
    (N : ℕ) [NeZero N] (hN : 0<N) :
    IsFinite (lpsOriginalIntegerNormalInfinityChartToJLine N hN) := by sorry
