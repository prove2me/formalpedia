-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerSpecZ_hom_unique
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerSpecZ_hom_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:54:43.341881+00:00
-- url     : https://prove2.me/theorems/7079dd58-e2a8-46b4-9e7a-59540c240975
-- title:
--   Tanner Lifted Product: lps Original Integer Spec Z hom unique
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Spec Z hom unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerProperModel.lean#L1000-L1005
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerProperModel.lean#L1000-L1005

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerSpecZ_hom_unique
    (R : Type) [CommRing R] (f g : Spec (.of R) ⟶ Spec (.of ℤ)) : f=g := by sorry
