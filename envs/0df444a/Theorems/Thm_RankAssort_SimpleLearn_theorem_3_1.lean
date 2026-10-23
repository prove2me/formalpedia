-- Prove2me | Theorems.Thm_RankAssort_SimpleLearn_theorem_3_1
-- name    : RankAssort.SimpleLearn.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:57:34.64423+00:00
-- url     : https://prove2.me/theorems/b31f02ea-d356-4098-835e-8168d21ec099
-- title:
--   Theorem 3 (1), pp. 22–23 — with probability 1 − δ the Simple Learning Algorithm's ranking hooks at least ½ of the optimum minus ϵ
-- statement:
--   Consider the online assortment ranking problem with $n$ products: customers have types $(p, f, k)$ drawn from an arbitrary distribution $\mathcal D$ (with a measurable type map), click sequentially with bias inside their first impression window, and are hooked if they click at least once. Let $\epsilon, \delta > 0$, and run the Simple Learning Algorithm (Algorithm 2) with any $(\epsilon', \delta')$-PAC algorithm as a black box, where
--
--   $$
--   \epsilon' = \frac{2\epsilon}{n}, \qquad \delta' = \frac{\delta}{n}.
--   $$
--
--   Then with probability at least $1-\delta$ the returned ranking $\tilde\pi$ satisfies, simultaneously for every ranking $\pi^*$ (in particular the optimal one),
--
--   $$
--   \mathbb E[H(\tilde\pi)] \ \ge\ \frac12\,\mathbb E[H(\pi^*)] - \epsilon .
--   $$
--
--   This is part 1 of Theorem 3 (general OnAR): learning with a black-box PAC bandit algorithm recovers, up to an additive $\epsilon$ and with confidence $1-\delta$, the factor ½ that the greedy algorithm attains with complete information (Theorem 1).
--
--   **Formalization Note** Ranks are 0-based in Lean: the paper's rank $r$ is index $r-1$, a ranking is a duplicate-free list of the $n$ products (`Fin n`), and $\pi^{-1}(j)$ is the list entry at index $j-1$. "Any $(\epsilon',\delta')$-PAC algorithm as a black box" is a `SimpleLearningRun D τ (2 * eps / n) (delta / n) P`: a random output ranking $\tilde\pi(\omega)$ whose rank-$r$ product, conditionally on every prefix already fixed, fails to be $\epsilon'$-approximately best among the unranked products with probability at most $\delta'$ (Definition 1 applied at each call, p. 58). The sampling of the black box is not modelled. $\mathbb E[H(\cdot)]$ is computed from the sequential click law with bias. "The optimal ranking" is rendered as "every ranking", which is equivalent since the set of rankings is finite. As on the page, only $\epsilon, \delta > 0$ are assumed; for $\delta \ge 1$ the statement is trivially true. Part 2 (Independence, $1-1/e$) is not formalized.
--
--   Differences from the source:
--   - reading: given any (ϵ′, δ′)-PAC algorithm as a black box (Definition 1) → a SimpleLearningRun: the output π̃(ω) whose rank-r product, conditionally on every prefix already fixed, fails to be ϵ′-best among the unranked products with probability ≤ δ′; the black box's sampling and T̃ are not modelled; reason: Algorithm 2 calls ALG once per rank on the unranked products, and p. 58 uses its guarantee "for any particular instantiation of [π̃]ᵣ₋₁"; T̃ does not enter the conclusion
--   - encoding: π∗ the optimal ranking → every ranking π∗, quantified inside the probability event; reason: equivalent: rankings form a finite nonempty set, so the optimum exists and the bound for it implies the bound for every ranking
--   - encoding: with probability (1 − δ) → ENNReal.ofReal (1 − delta) ≤ P {ω | …}; reason: Lean convention; same statement for δ ≤ 1, trivial for δ > 1 as on the page
--   - encoding: expectation over the type (p, f, k) ∼ D, a random variable → integral over θ ∼ D of a function of τ θ, with TypeMeasurable τ (every coordinate of the type map measurable); reason: the expectations are undefined otherwise (Lean would return the junk value 0); the integrands lie in [0, 1], so measurability is all that is needed
--   - encoding: ranks 1..n, a ranking is a permutation π of [n], π⁻¹(j) the product at rank j → 0-based indices, a ranking is a duplicate-free List (Fin n) of length n, π⁻¹(j) is the entry at index j − 1; reason: Lean convention; the same rankings
-- source:
--   Ferreira, Parthasarathy, Sekar, Learning to Rank an Assortment of Products, SSRN 3395992 author manuscript, pp. 22–23, Theorem 3 (part 1)

import Mathlib
import Definitions.Def_RankAssort_SimpleLearn_Model
import Definitions.Def_RankAssort_SimpleLearn_Algorithm

namespace RankAssort.SimpleLearn
open MeasureTheory
theorem theorem_3_1 {n : ℕ} {Θ : Type*} [MeasurableSpace Θ] (D : Measure Θ)
    [IsProbabilityMeasure D] (τ : Θ → CustomerType n) (hτ : TypeMeasurable τ)
    (eps delta : ℝ) (heps : 0 < eps) (hdelta : 0 < delta)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (run : SimpleLearningRun D τ (2 * eps / n) (delta / n) P) :
    ENNReal.ofReal (1 - delta) ≤
      P {ω | ∀ piStar : List (Fin n), piStar.Nodup → piStar.length = n →
              (1 / 2 : ℝ) * expHook D τ piStar - eps ≤ expHook D τ (run.out ω)} := by sorry
end RankAssort.SimpleLearn
