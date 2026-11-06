-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_LaurentFiniteWindow_laurentWindow_eq_span
-- name    : QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow.laurentWindow_eq_span
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:04:14.838561+00:00
-- url     : https://prove2.me/theorems/1b3660d5-d257-4000-801c-618fc7b8d88f
-- title:
--   Laurent Finite Window: laurent Window eq span
-- statement:
--   The Laurent Finite Window construction uses the laurent Window eq span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/LaurentFiniteWindow.lean#L76-L92
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/LaurentFiniteWindow.lean#L76-L92

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_LaurentFiniteWindow
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow
open scoped Polynomial Pointwise
variable (k : Type*) [Field k]

theorem QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow.laurentWindow_eq_span (lower upper : ℤ) :
    laurentWindow k lower upper =
      Submodule.span k (laurentWindowFamily k lower upper : Set (LaurentPolynomial k)) := by sorry
