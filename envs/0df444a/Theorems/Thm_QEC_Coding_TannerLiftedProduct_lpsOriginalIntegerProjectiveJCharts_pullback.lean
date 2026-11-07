-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerProjectiveJCharts_pullback
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerProjectiveJCharts_pullback
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:56:46.163104+00:00
-- url     : https://prove2.me/theorems/cfa54caf-cfbe-41e2-a31f-a8b866fc2e22
-- title:
--   Tanner Lifted Product: lps Original Integer Projective JCharts pullback
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Projective JCharts pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerProperModel.lean#L605-L642
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerProperModel.lean#L605-L642

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerProjectiveJCharts_pullback :
    IsPullback (lpsOriginalIntegerProjectiveJOverlapMap false)
      (lpsOriginalIntegerProjectiveJOverlapMap true)
      (lpsOriginalIntegerProjectiveJChartMap false)
      (lpsOriginalIntegerProjectiveJChartMap true) := by sorry
