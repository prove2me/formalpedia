-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerProjectiveJChartMap_cover
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerProjectiveJChartMap_cover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:55:49.129552+00:00
-- url     : https://prove2.me/theorems/52a00db8-5793-4725-beb3-a916b518d101
-- title:
--   Tanner Lifted Product: lps Original Integer Projective JChart Map cover
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Projective JChart Map cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerProperModel.lean#L352-L356
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerProperModel.lean#L352-L356

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerProjectiveJChartMap_cover
    (x : lpsOriginalIntegerProjectiveJLine) :
    ∃ (b : Bool) (y : Spec (.of (Polynomial ℤ))),
      lpsOriginalIntegerProjectiveJChartMap b y=x := by sorry
