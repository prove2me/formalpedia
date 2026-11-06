-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_LaurentFiniteWindow_direct_mul_inverse_support_subset
-- name    : QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow.direct_mul_inverse_support_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:03:58.354515+00:00
-- url     : https://prove2.me/theorems/ce10687d-b303-436f-944c-418b0cae8f2d
-- title:
--   Laurent Finite Window: direct mul inverse support subset
-- statement:
--   The Laurent Finite Window construction uses the direct mul inverse support subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/LaurentFiniteWindow.lean#L117-L127
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/LaurentFiniteWindow.lean#L117-L127

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_LaurentFiniteWindow
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow
open scoped Polynomial Pointwise
variable (k : Type*) [Field k]

theorem QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow.direct_mul_inverse_support_subset (p q : k[X]) :
    (directCoordinate k p * inverseCoordinate k q).coeff.support ⊆
      Finset.Icc (-(q.natDegree : ℤ)) (p.natDegree : ℤ) := by sorry
