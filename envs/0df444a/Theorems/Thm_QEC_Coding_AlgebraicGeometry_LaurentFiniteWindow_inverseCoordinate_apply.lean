-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_LaurentFiniteWindow_inverseCoordinate_apply
-- name    : QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow.inverseCoordinate_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:03:59.611194+00:00
-- url     : https://prove2.me/theorems/9f028c93-68be-4b02-96a8-213971642d0b
-- title:
--   Laurent Finite Window: inverse Coordinate apply
-- statement:
--   The Laurent Finite Window construction uses the inverse Coordinate apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/LaurentFiniteWindow.lean#L19-L21
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/LaurentFiniteWindow.lean#L19-L21

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_LaurentFiniteWindow
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow
open scoped Polynomial Pointwise
variable (k : Type*) [Field k]

theorem QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow.inverseCoordinate_apply (p : k[X]) :
    inverseCoordinate k p = LaurentPolynomial.invert p.toLaurent := by sorry
