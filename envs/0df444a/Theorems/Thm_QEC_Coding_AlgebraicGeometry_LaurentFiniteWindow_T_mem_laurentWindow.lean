-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_LaurentFiniteWindow_T_mem_laurentWindow
-- name    : QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow.T_mem_laurentWindow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:04:00.658619+00:00
-- url     : https://prove2.me/theorems/9ba89701-2b9e-4518-984f-664599835c87
-- title:
--   Laurent Finite Window: T mem laurent Window
-- statement:
--   The Laurent Finite Window construction uses the T mem laurent Window property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/LaurentFiniteWindow.lean#L61-L68
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/LaurentFiniteWindow.lean#L61-L68

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_LaurentFiniteWindow
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow
open scoped Polynomial Pointwise
variable (k : Type*) [Field k]

theorem QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow.T_mem_laurentWindow {lower upper n : ℤ} (hn : n ∈ Finset.Icc lower upper) :
    LaurentPolynomial.T (R := k) n ∈ laurentWindow k lower upper := by sorry
