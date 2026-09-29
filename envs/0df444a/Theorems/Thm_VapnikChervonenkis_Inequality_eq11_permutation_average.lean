-- Prove2me | Theorems.Thm_VapnikChervonenkis_Inequality_eq11_permutation_average
-- name    : VapnikChervonenkis.Inequality.eq11_permutation_average
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T00:17:17.158195+00:00
-- url     : https://prove2.me/theorems/503d1447-8360-4011-80bc-ac06f54a37bb
-- title:
--   Eq. (11) — $P\{\rho^{(l)} \ge \varepsilon/2\}$ as an integral of a permutation average
-- statement:
--   Let $(X, P)$ be a probability space and $S$ a collection of events, and assume that the semi-sample deviation $\rho^{(l)}$ is measurable for every $l$. A permutation $T$ of the $2l$ positions of a double sample $X_{2l} = (x_1, \dots, x_{2l})$ produces the rearranged sample $T X_{2l}$. Let $\theta(z) = 1$ for $z \ge 0$ and $\theta(z) = 0$ for $z < 0$. Then, for every real $\varepsilon$ and every $l$,
--   $$
--   P\Bigl\{\rho^{(l)} \ge \frac{\varepsilon}{2}\Bigr\} = \int_{X^{2l}} \frac{1}{(2l)!} \sum_{T} \theta\Bigl(\rho^{(l)}(T X_{2l}) - \frac{\varepsilon}{2}\Bigr)\, dP^{2l},
--   $$
--   the sum running over all $(2l)!$ permutations $T$.
--
--   The identity expresses the invariance of the product measure $P^{2l}$ under rearrangements of the sample; it reduces the estimate of $P\{\rho^{(l)} \ge \varepsilon/2\}$ to a bound on the fraction of rearrangements of one fixed sample.
--
--   **Formalization Note** $T X_{2l}$ is `x ∘ σ` for `σ : Equiv.Perm (Fin (l + l))`, and the average of $\theta(\rho^{(l)}(T X_{2l}) - \varepsilon/2)$ is the number of permutations with $\rho^{(l)}(x \circ \sigma) \ge \varepsilon/2$ divided by $(2l)!$. The left side is a value in $[0, \infty]$ and the right side the embedding of the real integral. The measurability of $\rho^{(l)}$ is the paper's standing assumption (p. 268).
-- source:
--   Vapnik and Chervonenkis, On the Uniform Convergence of Relative Frequencies of Events to Their Probabilities, Theory Probab. Appl. 16 (1971), p. 270, Eq. (11) (proof of Theorem 2)

import Mathlib
import Definitions.Def_VapnikChervonenkis_Shared_index
import Definitions.Def_VapnikChervonenkis_Shared_growthFunction
import Definitions.Def_VapnikChervonenkis_Shared_deviation

open MeasureTheory Filter Topology

namespace VapnikChervonenkis.Inequality

/-- **Eq. (11)** (p. 270): by the symmetry of the product measure under permutations `T_i` of
the double sample,
`P{ρ^(l) ≥ ε/2} = ∫ (1/(2l)!) Σ_i θ(ρ^(l)(T_i X_{2l}) − ε/2) dP`, the sum running over all
`(2l)!` permutations; `θ(ρ − ε/2)` is the indicator of `ρ ≥ ε/2`, and `T_i X_{2l}` is
`x ∘ σ`. -/
theorem eq11_permutation_average {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (S : Set (Set X))
    (hρ : ∀ l, Measurable (Shared.semiSampleDeviation S l)) (ε : ℝ) (l : ℕ) :
    Measure.pi (fun _ : Fin (l + l) => P) {x | ε / 2 ≤ Shared.semiSampleDeviation S l x}
      = ENNReal.ofReal (∫ x, ((Finset.univ.filter (fun σ : Equiv.Perm (Fin (l + l)) =>
            ε / 2 ≤ Shared.semiSampleDeviation S l (x ∘ σ))).card : ℝ) / ((l + l).factorial : ℝ)
          ∂(Measure.pi (fun _ : Fin (l + l) => P))) := by sorry

end VapnikChervonenkis.Inequality
