-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_rationalCoordinate_adjoin_finite_separable
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.rationalCoordinate_adjoin_finite_separable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:22:49.173878+00:00
-- url     : https://prove2.me/theorems/0f67ca12-b873-4305-9a09-042d0b82443a
-- title:
--   F256 Garcia Stichtenoth: rational Coordinate adjoin finite separable
-- statement:
--   The literal basic cell is finite and separable over its rational
--   coordinate base, by its already constructed degree-sixteen source model.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RationalCoordinateCells.lean#L86-L96
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RationalCoordinateCells.lean#L86-L96

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_CoordinateWindows
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RationalCoordinateCells
set_option autoImplicit false
open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.AmbientPlaceModels
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {E : Type*} [_root_.Field E] [Algebra F256 E]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.rationalCoordinate_adjoin_finite_separable (x y : E)
    (hx : Transcendental F256 x) (h : y ^ 16 + y = sourceStepRhs x) :
    FiniteDimensional F256⟮x⟯ (F256⟮x⟯)⟮y⟯ ∧
      Algebra.IsSeparable F256⟮x⟯ (F256⟮x⟯)⟮y⟯ := by sorry
