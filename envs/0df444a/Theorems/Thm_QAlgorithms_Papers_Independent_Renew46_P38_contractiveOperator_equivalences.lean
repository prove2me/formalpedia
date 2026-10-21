-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P38_contractiveOperator_equivalences
-- name    : QAlgorithms.Papers.Independent.Renew46.P38.contractiveOperator_equivalences
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:07:27.087602+00:00
-- url     : https://prove2.me/theorems/9349d3e2-d7a5-4557-9965-3e4fca477351
-- title:
--   Contractive operator Jensen equivalence
-- statement:
--   Let $I\subseteq\mathbb R$ be an interval containing $0$, and let $f:I\to\mathbb R$ be continuous. Then operator convexity of $f$ together with $f(0)\leq0$ is equivalent to the following property for some positive integer $n$, and is also equivalent to that property for every positive integer $n$: for every complex Hilbert space $H$, every self-adjoint $x_1,\ldots,x_n\in B(H)$ with spectra in $I$, and every $a_1,\ldots,a_n\in B(H)$ with $\sum_i a_i^*a_i\leq1$,
--   $$f\!\left(\sum_i a_i^*x_i a_i\right)\leq\sum_i a_i^*f(x_i)a_i.$$
--   The integer in the existential version is chosen uniformly before $H$ and all the input operators. This gives the contractive counterpart of unital Jensen and includes the one-term characterization.
-- source:
--   Jensen's Operator Inequality, arXiv:math/0204049v1, PDF p. 3, Corollary 2.3 (Contractive Version)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P38

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal

namespace QAlgorithms.Papers.Independent.Renew46.P38

universe u

/-- Hansen--Pedersen, Corollary 2.3, PDF p. 3 (proof p. 8).
The existential tuple size precedes every Hilbert space and every input. -/
theorem contractiveOperator_equivalences (I : Set ℝ) (f : ℝ → ℝ)
    (hI : Set.OrdConnected I) (hf : ContinuousOn f I) (hzero : 0 ∈ I) :
    ((IntervalOperatorConvex.{u} I f ∧ f 0 ≤ 0) ↔
      ∃ n : ℕ, 1 ≤ n ∧ AllContractiveJensen.{u} I f n) ∧
    ((IntervalOperatorConvex.{u} I f ∧ f 0 ≤ 0) ↔
      ∀ n : ℕ, 1 ≤ n → AllContractiveJensen.{u} I f n) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P38

end
