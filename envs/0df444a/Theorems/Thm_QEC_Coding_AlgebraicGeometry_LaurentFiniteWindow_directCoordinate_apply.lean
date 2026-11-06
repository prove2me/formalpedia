-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_LaurentFiniteWindow_directCoordinate_apply
-- name    : QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow.directCoordinate_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:03:30.973424+00:00
-- url     : https://prove2.me/theorems/1957fc4c-e058-4309-9ed5-41e045a9b8a2
-- title:
--   Laurent Finite Window: direct Coordinate apply
-- statement:
--   The Laurent Finite Window construction uses the direct Coordinate apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/LaurentFiniteWindow.lean#L15-L17
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/LaurentFiniteWindow.lean#L15-L17

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_LaurentFiniteWindow
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow
open scoped Polynomial Pointwise
variable (k : Type*) [Field k]

theorem QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow.directCoordinate_apply (p : k[X]) :
    directCoordinate k p = p.toLaurent := by sorry
