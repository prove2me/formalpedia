-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_LaurentFiniteWindow_direct_mul_inverse_mem_laurentWindow
-- name    : QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow.direct_mul_inverse_mem_laurentWindow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:30:04.944502+00:00
-- url     : https://prove2.me/theorems/4bc7df66-750a-4f23-8d0d-f0df62edea55
-- title:
--   Laurent Finite Window: direct mul inverse mem laurent Window
-- statement:
--   The Laurent Finite Window construction uses the direct mul inverse mem laurent Window property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/LaurentFiniteWindow.lean#L129-L134
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/LaurentFiniteWindow.lean#L129-L134

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_LaurentFiniteWindow
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow
open scoped Polynomial Pointwise
variable (k : Type*) [Field k]

theorem QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow.direct_mul_inverse_mem_laurentWindow (p q : k[X]) :
    directCoordinate k p * inverseCoordinate k q ∈
      laurentWindow k (-(q.natDegree : ℤ)) (p.natDegree : ℤ) := by sorry
