-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P38_jensenOperator_equivalences
-- name    : QAlgorithms.Papers.Independent.Renew46.P38.jensenOperator_equivalences
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T21:06:17.252893+00:00
-- url     : https://prove2.me/theorems/3f17cddb-b46f-4d4c-b5ea-3b9d0ddd38bc
-- title:
--   Jensen’s operator inequality: four equivalent conditions
-- statement:
--   Let $I\subseteq\mathbb R$ be an interval and let $f:I\to\mathbb R$ be continuous. For a bounded self-adjoint operator $x$ with spectrum in $I$, write $f(x)$ for its continuous functional calculus. The following four conditions are equivalent:
--
--   1. The operator function $f$ is convex on every infinite-dimensional complex Hilbert space.
--   2. For every positive integer $n$, every complex Hilbert space $H$, self-adjoint $x_1,\ldots,x_n\in B(H)$ with spectra in $I$, and $a_1,\ldots,a_n\in B(H)$ satisfying $\sum_i a_i^*a_i=1$,
--   $$f\!\left(\sum_i a_i^*x_i a_i\right)\leq\sum_i a_i^*f(x_i)a_i.$$
--   3. For every infinite-dimensional $H$, every isometry $v\in B(H)$, and every such $x$, $f(v^*xv)\leq v^*f(x)v$.
--   4. For every infinite-dimensional $H$, orthogonal projection $p\in B(H)$, such $x$, and $s\in I$,
--   $$p f(pxp+s(1-p))p\leq p f(x)p.$$
--
--   All operator comparisons are in the Loewner order. This characterizes operator convexity without conditions on $f(0)$ or on whether $0$ belongs to $I$.
-- source:
--   Jensen's Operator Inequality, arXiv:math/0204049v1, PDF p. 3, Theorem 2.1 (Jensen’s Operator Inequality)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P38

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal

namespace QAlgorithms.Papers.Independent.Renew46.P38

universe u

/-- Hansen--Pedersen, Theorem 2.1, PDF p. 3 (proof pp. 6--8).
All four conditions are equivalent. The fourth label is printed (vi), called (iv)
in the proof. No condition 0 ∈ I or f(0) ≤ 0 is imposed. -/
theorem jensenOperator_equivalences (I : Set ℝ) (f : ℝ → ℝ)
    (hI : Set.OrdConnected I) (hf : ContinuousOn f I) :
    (IntervalOperatorConvex.{u} I f ↔ ∀ n : ℕ, 1 ≤ n → AllUnitalJensen.{u} I f n) ∧
    (IntervalOperatorConvex.{u} I f ↔ IsometryJensen.{u} I f) ∧
    (IntervalOperatorConvex.{u} I f ↔ PinchingJensen.{u} I f) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P38

end
