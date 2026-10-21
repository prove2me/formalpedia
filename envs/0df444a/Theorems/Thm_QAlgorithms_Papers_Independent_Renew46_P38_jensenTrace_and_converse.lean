-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P38_jensenTrace_and_converse
-- name    : QAlgorithms.Papers.Independent.Renew46.P38.jensenTrace_and_converse
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T21:08:09.175953+00:00
-- url     : https://prove2.me/theorems/dd60f3c3-f556-459f-88bc-e28b9ba57203
-- title:
--   Jensen’s matrix trace inequality and its converse
-- statement:
--   Let $I$ be a real interval and $f:I\to\mathbb R$ continuous. If $f$ is convex, then for all positive integers $m,n$, self-adjoint complex $m\times m$ matrices $x_1,\ldots,x_n$ with spectra in $I$, and complex $m\times m$ matrices $a_1,\ldots,a_n$ satisfying $\sum_i a_i^*a_i=1$,
--   $$\operatorname{Tr}\!\left(f\!\left(\sum_i a_i^*x_i a_i\right)\right)\leq\operatorname{Tr}\!\left(\sum_i a_i^*f(x_i)a_i\right).$$
--   Conversely, if this inequality holds for all such inputs at some fixed $m\geq1$ and $n\geq2$, then $f$ is convex on $I$.
--
--   The trace is unnormalized. Its real part is used formally, which agrees with the trace on these self-adjoint expressions. The result characterizes scalar convexity through a fixed nonzero matrix dimension.
-- source:
--   Jensen's Operator Inequality, arXiv:math/0204049v1, PDF p. 3, Theorem 2.4 (Jensen’s Trace Inequality)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P38

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal

namespace QAlgorithms.Papers.Independent.Renew46.P38

universe u

/-- Hansen--Pedersen, Theorem 2.4, PDF p. 3 (proof pp. 8--9).
The converse requires positive m and n>1. In the proof, i≥2 is a typo for i>2;
the scalar reduction in (30) uses x=s1_m and y=t1_m. -/
theorem jensenTrace_and_converse (I : Set ℝ) (f : ℝ → ℝ)
    (hI : Set.OrdConnected I) (hf : ContinuousOn f I) :
    (ConvexOn ℝ I f → ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
      MatrixTraceJensen I f m n false) ∧
    ((∃ m n : ℕ, 1 ≤ m ∧ 2 ≤ n ∧ MatrixTraceJensen I f m n false) →
      ConvexOn ℝ I f) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P38

end
