-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coordinateWindow_normalized_prefix
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coordinateWindow_normalized_prefix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:21:19.371415+00:00
-- url     : https://prove2.me/theorems/0042e3ab-d336-4645-8380-05e03d10355f
-- title:
--   F256 Garcia Stichtenoth: coordinate Window normalized prefix
-- statement:
--   The left side of the finite pyramid is the whole original coordinate
--   chain, refined into normalized quadratic steps at the fixed ambient place.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/CoordinateWindows.lean#L133-L152
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/CoordinateWindows.lean#L133-L152

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_PlaceRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_CoordinateWindows
set_option autoImplicit false
open IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {E : Type*} [_root_.Field E] [Algebra F256 E]
variable (Q : GlobalPlace F256 E) [Finite Q.residueField] (x : ℕ → E)
    [∀ a, FiniteDimensional F256⟮x a⟯ E]
    [∀ a, Algebra.IsSeparable F256⟮x a⟯ E]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coordinateWindow_normalized_prefix (N : ℕ)
    (hbasic : ∀ a, a < N →
      PlaceNormalizedExtension Q (coordinateWindow x a 0) (coordinateWindow x a 1) ∧
      PlaceNormalizedExtension Q (coordinateWindow x (a + 1) 0) (coordinateWindow x a 1)) :
    ∀ n, n ≤ N → PlaceNormalizedExtension Q (coordinateWindow x 0 0)
      (coordinateWindow x 0 n) := by sorry
