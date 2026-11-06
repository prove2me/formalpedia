-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_LaurentFiniteWindow_opposite_scaled_intersection_mem_laurentWindow
-- name    : QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow.opposite_scaled_intersection_mem_laurentWindow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:29:50.582512+00:00
-- url     : https://prove2.me/theorems/f7c53985-a5f0-4e15-95da-784905bab564
-- title:
--   Laurent Finite Window: opposite scaled intersection mem laurent Window
-- statement:
--   The Laurent Finite Window construction uses the opposite scaled intersection mem laurent Window property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/LaurentFiniteWindow.lean#L142-L171
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/LaurentFiniteWindow.lean#L142-L171

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_LaurentFiniteWindow
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow
open scoped Polynomial Pointwise
variable (k : Type*) [Field k]

theorem QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow.opposite_scaled_intersection_mem_laurentWindow
    {a b : k[X]} {z : LaurentPolynomial k}
    (hzDirect : z ∈ directScaledLocus k a)
    (hzInverse : z ∈ inverseScaledLocus k b) :
    inverseCoordinate k b * (directCoordinate k a * z) ∈
      laurentWindow k (-(b.natDegree : ℤ)) (a.natDegree : ℤ) := by sorry
