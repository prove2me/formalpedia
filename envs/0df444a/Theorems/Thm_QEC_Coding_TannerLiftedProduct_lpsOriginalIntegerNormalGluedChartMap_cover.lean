-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedChartMap_cover
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedChartMap_cover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:56:28.379784+00:00
-- url     : https://prove2.me/theorems/7b3d38f1-7c86-46de-8f6f-ccc36f5e7263
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Glued Chart Map cover
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal Glued Chart Map cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerProperModel.lean#L169-L173
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerProperModel.lean#L169-L173

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedChartMap_cover
    (N : ℕ) (hN : 0<N) (x : lpsOriginalIntegerNormalGluedScheme N hN) :
    ∃ (b : Bool) (y : lpsOriginalIntegerNormalSchemeChart N hN b),
      lpsOriginalIntegerNormalGluedChartMap N hN b y=x := by sorry
