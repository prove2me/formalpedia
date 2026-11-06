-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_rationalCoordinateWindow_normalized
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.rationalCoordinateWindow_normalized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:23:07.888682+00:00
-- url     : https://prove2.me/theorems/1dccfb31-65db-4f04-ab09-788b60f4ff9b
-- title:
--   F256 Garcia Stichtenoth: rational Coordinate Window normalized
-- statement:
--   The complete source pyramid for literal recursion coordinates. The
--   displayed source equations provide both basic projections, so no
--   normalized higher-window input remains.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RationalCoordinateCells.lean#L131-L143
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RationalCoordinateCells.lean#L131-L143

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_CoordinateWindows
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RationalCoordinateCells
set_option autoImplicit false
open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.AmbientPlaceModels
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {E : Type*} [_root_.Field E] [Algebra F256 E]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.rationalCoordinateWindow_normalized
    (Q : GlobalPlace F256 E) [Finite Q.residueField]
    (x : ℕ → E) [∀ a, FiniteDimensional F256⟮x a⟯ E]
    [∀ a, Algebra.IsSeparable F256⟮x a⟯ E]
    (hx : ∀ a, Transcendental F256 (x a)) (N : ℕ)
    (hrec : ∀ a, a < N → x (a + 1) ^ 16 + x (a + 1) = sourceStepRhs (x a)) :
    PlaceNormalizedExtension Q F256⟮x 0⟯ (coordinateWindow x 0 N) := by sorry
