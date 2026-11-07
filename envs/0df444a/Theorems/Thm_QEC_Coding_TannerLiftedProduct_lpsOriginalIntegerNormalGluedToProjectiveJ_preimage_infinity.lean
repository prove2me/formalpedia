-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedToProjectiveJ_preimage_infinity
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedToProjectiveJ_preimage_infinity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:00:59.722855+00:00
-- url     : https://prove2.me/theorems/7c9e3884-4726-4a82-bf5a-76a409b02b0c
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Glued To Projective J preimage infinity
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal Glued To Projective J preimage infinity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerProperModel.lean#L692-L728
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerProperModel.lean#L692-L728

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedToProjectiveJ_preimage_infinity
    (N : ℕ) (hN : 0<N) :
    lpsOriginalIntegerNormalGluedToProjectiveJ N hN ⁻¹'
      Set.range (lpsOriginalIntegerProjectiveJChartMap true) =
    Set.range (lpsOriginalIntegerNormalGluedChartMap N hN true) := by sorry
