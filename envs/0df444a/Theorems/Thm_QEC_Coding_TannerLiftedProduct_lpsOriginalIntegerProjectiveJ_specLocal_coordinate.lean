-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerProjectiveJ_specLocal_coordinate
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerProjectiveJ_specLocal_coordinate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:57:32.089204+00:00
-- url     : https://prove2.me/theorems/b1cf465a-4d73-4315-9eec-bbe8d92e80c6
-- title:
--   Tanner Lifted Product: lps Original Integer Projective J spec Local coordinate
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Projective J spec Local coordinate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerProperModel.lean#L940-L955
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerProperModel.lean#L940-L955

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerProjectiveJ_specLocal_coordinate
    (R : Type) [CommRing R] [IsLocalRing R]
    (f : Spec (.of R) ⟶ lpsOriginalIntegerProjectiveJLine) :
    ∃ (b : Bool) (x : R), f=lpsOriginalIntegerProjectiveJAffinePoint R b x := by sorry
