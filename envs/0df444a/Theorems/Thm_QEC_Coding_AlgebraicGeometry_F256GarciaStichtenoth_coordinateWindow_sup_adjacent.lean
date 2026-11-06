-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coordinateWindow_sup_adjacent
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coordinateWindow_sup_adjacent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:21:23.942201+00:00
-- url     : https://prove2.me/theorems/6936091d-b046-4eaa-a6fe-2a8bea7b13ee
-- title:
--   F256 Garcia Stichtenoth: coordinate Window sup adjacent
-- statement:
--   The two overlapping windows in one source-pyramid square generate
--   exactly the next whole window.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/CoordinateWindows.lean#L71-L78
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/CoordinateWindows.lean#L71-L78

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_PlaceRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_CoordinateWindows
set_option autoImplicit false
open IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {E : Type*} [_root_.Field E] [Algebra F256 E]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coordinateWindow_sup_adjacent (x : ℕ → E) (a n : ℕ) :
    coordinateWindow x a (n + 1) ⊔ coordinateWindow x (a + 1) (n + 1) =
      coordinateWindow x a (n + 2) := by sorry
