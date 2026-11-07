-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerProjectiveJAffinePoint_unitInverse
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerProjectiveJAffinePoint_unitInverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:58:47.476195+00:00
-- url     : https://prove2.me/theorems/cc4471ae-6f90-4edf-9d13-42b8a0b817e1
-- title:
--   Tanner Lifted Product: lps Original Integer Projective JAffine Point unit Inverse
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Projective JAffine Point unit Inverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerProperModel.lean#L970-L992
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerProperModel.lean#L970-L992

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerProjectiveJAffinePoint_unitInverse
    (R : Type) [CommRing R] (u : Rˣ) :
    lpsOriginalIntegerProjectiveJAffinePoint R false (u : R) =
      lpsOriginalIntegerProjectiveJAffinePoint R true ((u⁻¹ : Rˣ) : R) := by sorry
