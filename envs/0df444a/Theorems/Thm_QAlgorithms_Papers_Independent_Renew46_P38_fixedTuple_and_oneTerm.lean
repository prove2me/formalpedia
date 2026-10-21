-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P38_fixedTuple_and_oneTerm
-- name    : QAlgorithms.Papers.Independent.Renew46.P38.fixedTuple_and_oneTerm
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:06:47.515945+00:00
-- url     : https://prove2.me/theorems/3614c745-f907-49e1-bb8b-a9101ae66c3e
-- title:
--   Fixed tuple size and the one-term specialization
-- statement:
--   Let $I$ be a real interval, $f:I\to\mathbb R$ continuous, and $H$ a complex Hilbert space. Write $J_n(H)$ for the assertion that, for every self-adjoint $x_i\in B(H)$ with spectra in $I$ and every column $a_i\in B(H)$ with $\sum_i a_i^*a_i=1$,
--   $$f\!\left(\sum_{i=1}^n a_i^*x_i a_i\right)\leq\sum_{i=1}^n a_i^*f(x_i)a_i.$$
--   For every $n\geq2$, $J_n(H)$ implies convexity of the operator function on this particular $B(H)$. If $H$ is infinite-dimensional, $J_1(H)$ already implies that local convexity. For every $n\geq1$, $J_n(H)$ implies $J_1(H)$.
--
--   In finite dimension $m$, the local conclusion is matrix convexity of order $m$. No finite-dimensional one-term converse is asserted. These observations distinguish fixed-space convexity from operator convexity over arbitrary spaces.
-- source:
--   Jensen's Operator Inequality, arXiv:math/0204049v1, PDF p. 3, Remark 2.2: fixed tuple size and the one-term specialization

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P38

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal

namespace QAlgorithms.Papers.Independent.Renew46.P38

universe u

/-- Hansen--Pedersen, Remark 2.2, PDF p. 3.
The first conclusion is local convexity on B(H); for finite H it is only matrix
convexity at that dimension. One term suffices on infinite-dimensional H. -/
theorem fixedTuple_and_oneTerm (I : Set ℝ) (f : ℝ → ℝ)
    (hI : Set.OrdConnected I) (hf : ContinuousOn f I)
    (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    (∀ n : ℕ, 2 ≤ n → UnitalJensenOn H I f n → ConvexOnOperators H I f) ∧
    ((¬ FiniteDimensional ℂ H) → UnitalJensenOn H I f 1 → ConvexOnOperators H I f) ∧
    (∀ n : ℕ, 1 ≤ n → UnitalJensenOn H I f n → UnitalJensenOn H I f 1) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P38

end
