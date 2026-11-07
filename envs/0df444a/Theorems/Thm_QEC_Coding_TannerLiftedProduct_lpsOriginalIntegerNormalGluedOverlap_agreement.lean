-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedOverlap_agreement
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedOverlap_agreement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:56:03.300237+00:00
-- url     : https://prove2.me/theorems/c66a8d4c-4a33-4eaa-a718-edc511b14c68
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Glued Overlap agreement
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal Glued Overlap agreement property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerProperModel.lean#L176-L207
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerProperModel.lean#L176-L207

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
set_option backward.isDefEq.respectTransparency false

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedOverlap_agreement
    (N : ℕ) (hN : 0<N) :
    lpsOriginalIntegerNormalSchemeOverlapMap N hN false ≫
      lpsOriginalIntegerNormalGluedChartMap N hN false=
    lpsOriginalIntegerNormalSchemeOverlapMap N hN true ≫
      lpsOriginalIntegerNormalGluedChartMap N hN true := by sorry
