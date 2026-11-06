-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_LaurentFiniteWindow_direct_support_subset_interval
-- name    : QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow.direct_support_subset_interval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:03:51.821205+00:00
-- url     : https://prove2.me/theorems/9793380a-02a0-4835-83e9-4a2756c32af5
-- title:
--   Laurent Finite Window: direct support subset interval
-- statement:
--   The Laurent Finite Window construction uses the direct support subset interval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/LaurentFiniteWindow.lean#L99-L105
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/LaurentFiniteWindow.lean#L99-L105

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_LaurentFiniteWindow
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow
open scoped Polynomial Pointwise
variable (k : Type*) [Field k]

theorem QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow.direct_support_subset_interval (p : k[X]) :
    (directCoordinate k p).coeff.support ⊆ Finset.Icc (0 : ℤ) (p.natDegree : ℤ) := by sorry
