-- Prove2me | Theorems.Thm_VapnikChervonenkis_Entropy_permutation_bound
-- name    : VapnikChervonenkis.Entropy.permutation_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T01:07:51.040699+00:00
-- url     : https://prove2.me/theorems/6521c8e3-9d69-4752-be14-37e917c72d6e
-- title:
--   Permutation bound — share of permutations with ρ^(l) ≥ ε/2 is at most 2Δ^S e^{−ε²l/8}
-- statement:
--   Let $S$ be a collection of subsets of a set $X$, let $l \ge 1$, $\varepsilon > 0$, and let $x_1, \dots, x_{2l}$ be a fixed sample of size $2l$. For a permutation $T$ of the $2l$ positions write $T X_{2l}$ for the permuted sample. Then
--
--   $$
--   \frac{1}{(2l)!} \sum_{T} \theta\Bigl(\rho^{(l)}(T X_{2l}) - \frac{\varepsilon}{2}\Bigr) \le 2\, \Delta^S(x_1, \dots, x_{2l})\, e^{-\varepsilon^2 l/8},
--   $$
--
--   where the sum runs over all $(2l)!$ permutations and $\theta(z) = 1$ for $z \ge 0$, $\theta(z) = 0$ for $z < 0$; the left side is the fraction of permutations for which $\rho^{(l)}(T X_{2l}) \ge \varepsilon/2$.
--
--   This deterministic estimate is where the index enters the probability bounds: averaged over $P^{2l}$ it bounds $\mathbf{P}(C)$ in the sufficiency proof of Theorem 4.
--
--   **Formalization Note.** Permutations are `Equiv.Perm (Fin (l + l))` and the permuted sample is `x ∘ σ`. The paper derives the bound from the estimate $\Gamma \le 2e^{-\varepsilon^2 l/8}$ of a hypergeometric tail (p. 271), whose proof it omits.
-- source:
--   Vapnik and Chervonenkis, On the Uniform Convergence of Relative Frequencies of Events to Their Probabilities, Theory Probab. Appl. 16 (1971), p. 271, Subsection 4 (display after "Thus,"), recalled on p. 276 in the proof of sufficiency of Theorem 4

import Mathlib
import Definitions.Def_VapnikChervonenkis_Shared_index
import Definitions.Def_VapnikChervonenkis_Shared_deviation

open MeasureTheory Filter Topology

namespace VapnikChervonenkis.Entropy

/-- **The per-sample permutation bound** (p. 271, recalled on p. 276: "In Subsection 4 it was
shown that …"): for every fixed double sample `x = (x_1, …, x_{2l})`, the fraction of the `(2l)!`
permutations `σ` for which the permuted sample `x ∘ σ` has `ρ^(l) ≥ ε/2` is at most
`2 Δ^S(x_1, …, x_{2l}) e^{−ε² l / 8}`. No measure is involved. -/
theorem permutation_bound {X : Type*} (S : Set (Set X)) (ε : ℝ) (l : ℕ) (hl : 1 ≤ l)
    (hε : 0 < ε) (x : Fin (l + l) → X) :
    ((Finset.univ.filter (fun σ : Equiv.Perm (Fin (l + l)) =>
        ε / 2 ≤ Shared.semiSampleDeviation S l (x ∘ σ))).card : ℝ) / ((l + l).factorial : ℝ)
      ≤ 2 * (Shared.index S x : ℝ) * Real.exp (-(ε ^ 2 * l / 8)) := by sorry

end VapnikChervonenkis.Entropy
