-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_exists_simplePoleRatio_square_add_maximalIdeal
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.exists_simplePoleRatio_square_add_maximalIdeal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:05:59.459682+00:00
-- url     : https://prove2.me/theorems/6d4c8002-7d03-4010-9783-20cf3e5e130b
-- title:
--   F256 Garcia Stichtenoth: exists simple Pole Ratio square add maximal Ideal
-- statement:
--   The ratio of two actual normalized simple-pole parameters is a unit square
--   plus a maximal-ideal error.  This is the precise residue-field cancellation
--   input used in the later two-extension compositum argument.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ArtinSchreierCancellation.lean#L162-L191
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ArtinSchreierCancellation.lean#L162-L191

import Mathlib.FieldTheory.Perfect
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_TwoChartGlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ArtinSchreierCancellation
set_option autoImplicit false
open scoped Polynomial RatFunc WithZero
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
variable [Algebra (Polynomial F256) K] [Algebra (RatFunc F256) K]
variable [IsScalarTower (Polynomial F256) (RatFunc F256) K]
variable [_root_.FunctionField F256 K]
variable [Algebra.IsSeparable (RatFunc F256) K]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.exists_simplePoleRatio_square_add_maximalIdeal
    (P : GlobalPlace F256 K) (z₁ z₂ : K)
    (hz₁ : P.order z₁ = -1) (hz₂ : P.order z₂ = -1) :
    ∃ u w : P.valuationRing,
      z₂ / z₁ = (u : K) ^ 2 + (w : K) ∧
        u ∉ IsLocalRing.maximalIdeal P.valuationRing ∧
        w ∈ IsLocalRing.maximalIdeal P.valuationRing := by sorry
