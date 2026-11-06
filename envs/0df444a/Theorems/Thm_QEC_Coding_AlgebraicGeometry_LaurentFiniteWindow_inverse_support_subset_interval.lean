-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_LaurentFiniteWindow_inverse_support_subset_interval
-- name    : QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow.inverse_support_subset_interval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:04:15.137635+00:00
-- url     : https://prove2.me/theorems/bb576875-1ed7-4312-81b4-6ce692ab834d
-- title:
--   Laurent Finite Window: inverse support subset interval
-- statement:
--   The Laurent Finite Window construction uses the inverse support subset interval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/LaurentFiniteWindow.lean#L107-L115
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/LaurentFiniteWindow.lean#L107-L115

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_LaurentFiniteWindow
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow
open scoped Polynomial Pointwise
variable (k : Type*) [Field k]

theorem QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow.inverse_support_subset_interval (q : k[X]) :
    (inverseCoordinate k q).coeff.support ⊆ Finset.Icc (-(q.natDegree : ℤ)) 0 := by sorry
