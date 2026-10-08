-- Prove2me | Theorems.Thm_SmithHitAndRun_RandomDir_lemma_1_uniform_stationary
-- name    : SmithHitAndRun.RandomDir.lemma_1_uniform_stationary
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:23:21.990979+00:00
-- url     : https://prove2.me/theorems/dbc1d888-6864-453a-8954-cf452b85144e
-- title:
--   Lemma 1 for the Random Directions Algorithm — the uniform distribution is stationary
-- statement:
--   Let $n\ge1$, let $S\subseteq\mathbb R^n$ be open, bounded and nonempty, let $P(\cdot\mid x)$ be the transition kernel of the Random Directions Algorithm over $S$ and $\lambda(A)=V(A)/V(S)$ the uniform distribution over $S$. Then for every measurable $A\subseteq S$,
--   $$\lambda(A)=\int_S P(A\mid x)\,\lambda(\mathrm dx).$$
--
--   In words: if $X_0$ is uniform over $S$, then so is $X_1$, and hence every $X_i$. This is the stationary law toward which Theorem 3 measures the distance.
--
--   **Formalization Note** The paper states Lemma 1 for every symmetric mixing algorithm satisfying Assumption (a); this item is its instance for the Random Directions Algorithm, with no assumption on the kernel beyond its definition.
-- source:
--   Smith, Efficient Monte Carlo Procedures for Generating Points Uniformly Distributed over Bounded Regions, Oper. Res. 32(6) (1984), p. 1300, Lemma 1

import Mathlib
import Definitions.Def_SmithHitAndRun_RandomDir_RandomDirectionsKernel
import Definitions.Def_SmithHitAndRun_RandomDir_UniformLaw

open MeasureTheory ProbabilityTheory

namespace SmithHitAndRun.RandomDir

/-- Smith 1984, p. 1300, Lemma 1, for the Random Directions Algorithm: the uniform distribution
`λ` over an open bounded region `S ⊆ ℝⁿ` is stationary, `λ(A) = ∫_S P(A | x) λ(dx)` for every
measurable `A ⊆ S`. -/
theorem lemma_1_uniform_stationary {n : ℕ} (hn : 1 ≤ n)
    (S : Set (EuclideanSpace ℝ (Fin n))) (hSo : IsOpen S) (hSb : Bornology.IsBounded S)
    (hSne : S.Nonempty) (A : Set (EuclideanSpace ℝ (Fin n))) (hA : MeasurableSet A)
    (hAS : A ⊆ S) :
    unif S A = ∫⁻ x in S, rdKernel S x A ∂(unif S) := by sorry

end SmithHitAndRun.RandomDir
