-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_LaurentFiniteWindow_laurentWindow_finiteDimensional
-- name    : QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow.laurentWindow_finiteDimensional
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:04:47.836923+00:00
-- url     : https://prove2.me/theorems/c7ef7a41-109b-4862-ad5d-988ecd59a0ff
-- title:
--   Laurent Finite Window: laurent Window finite Dimensional
-- statement:
--   The Laurent Finite Window construction uses the laurent Window finite Dimensional property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/LaurentFiniteWindow.lean#L94-L97
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/LaurentFiniteWindow.lean#L94-L97

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_LaurentFiniteWindow
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow
open scoped Polynomial Pointwise
variable (k : Type*) [Field k]

theorem QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow.laurentWindow_finiteDimensional (lower upper : ℤ) :
    FiniteDimensional k (laurentWindow k lower upper) := by sorry
