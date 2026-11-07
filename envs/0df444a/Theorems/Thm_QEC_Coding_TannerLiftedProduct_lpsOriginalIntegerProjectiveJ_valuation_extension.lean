-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerProjectiveJ_valuation_extension
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerProjectiveJ_valuation_extension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:02:44.214145+00:00
-- url     : https://prove2.me/theorems/41bd3373-025a-4e1a-ac0d-6937e74e6934
-- title:
--   Tanner Lifted Product: lps Original Integer Projective J valuation extension
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Projective J valuation extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerProperModel.lean#L1014-L1035
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerProperModel.lean#L1014-L1035

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerProjectiveJ_valuation_extension
    (R K : Type) [CommRing R] [IsDomain R] [ValuationRing R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (f : Spec (.of K) ⟶ lpsOriginalIntegerProjectiveJLine) :
    ∃ g : Spec (.of R) ⟶ lpsOriginalIntegerProjectiveJLine,
      Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ g=f := by sorry
