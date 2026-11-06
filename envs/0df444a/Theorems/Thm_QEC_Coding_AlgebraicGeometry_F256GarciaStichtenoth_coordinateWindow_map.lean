-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coordinateWindow_map
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coordinateWindow_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:20:53.775209+00:00
-- url     : https://prove2.me/theorems/808d3f73-564e-4719-824f-db43da138b5e
-- title:
--   F256 Garcia Stichtenoth: coordinate Window map
-- statement:
--   The F256 Garcia Stichtenoth construction uses the coordinate Window map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/CoordinateWindows.lean#L60-L67
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/CoordinateWindows.lean#L60-L67

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_PlaceRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_CoordinateWindows
set_option autoImplicit false
open IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {E : Type*} [_root_.Field E] [Algebra F256 E]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coordinateWindow_map {L : Type*} [_root_.Field L] [Algebra F256 L]
    (f : E →ₐ[F256] L) (x : ℕ → E) (a n : ℕ) :
    (coordinateWindow x a n).map f = coordinateWindow (fun i => f (x i)) a n := by sorry
