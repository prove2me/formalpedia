-- Prove2me | Theorems.Thm_PagingDelay_PMD_proposition_21
-- name    : PagingDelay.PMD.proposition_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:49:11.168823+00:00
-- url     : https://prove2.me/theorems/5b27a602-4be5-4860-999b-5d26d2a2a52b
-- title:
--   Proposition 21 — critical fetch cost against offline cost and excess
-- statement:
--   There are absolute positive constants $C_1,C_2$, chosen before all page counts, cache sizes, weights, initializations, tie orders, instances and offline schedules, such that
--
--   $$C^{\rm crit}_{\rm fetch}\le C_1L\operatorname{cost}(O)+\operatorname{Exc}+C_2L\sum_iw_i.$$
--
--   Here $O$ is any lazy feasible offline schedule from the same initial cache. Excess is evaluated against $O$ after its updates at each service time. Its coefficient is exactly one.
--
--   Differences from the source:
--   - encoding: finite pages, continuous time, finite requests and instantaneous cache walks → Fin n pages, real times, finite request and event lists, and ENNReal costs; reason: same instances; positive weights reduce every finite-cost offline schedule to finitely many fetches without increasing cost
--   - reading: any tie-breaking rule suffices → all page orders π and all designated initial pages i₀ outside O₀; reason: an arbitrary order resolves simultaneous critical times and equal effective deadlines; no order is fixed
--   - encoding: Algorithm 1 with instantaneous services and eventual service → explicit transition recursion with |σ|+1 next-event iterations, transient states, optional infima and zero-denominator guards; reason: each critical service serves a pending request, so there are at most |σ|; the guards only totalize undefined inputs, and Lemma 2 states full service rather than assuming it
--   - encoding: the first nonnegative hitting time |λ| and natural logarithm L → guarded real infimum and L = log(2k+1); reason: on the stated valid domain the hitting set is nonempty, bounded below and closed; k≥1 makes L positive
--   - generalization: an optimal lazy offline schedule Opt → every lazy feasible offline schedule O, with cost(O) on the right; reason: the source proofs use only laziness and service of every request; an optimal lazy schedule is one such comparator
-- source:
--   Julian Born, Yann Disser, Linda Thelen, Tight weighted paging with delay via mirror descent, STOC 2027 submission #453 (October 2026), Proposition 21 — critical fetch cost against offline cost and excess, p. 19. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/453.pdf

import Definitions.Def_PagingDelay_PMD_Algorithm

namespace PagingDelay.PMD
open scoped BigOperators

/-- Julian Born, Yann Disser, Linda Thelen, Tight weighted paging with delay via mirror descent, STOC 2027 submission #453 (October 2026), Proposition 21 — critical fetch cost against offline cost and excess, p. 19. -/
theorem proposition_21  :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (n k : ℕ) (hk : 1 ≤ k) (hkn : k < n)
    (w : Fin n → ℝ) (hw : PMDWeights w)
    (O₀ : Finset (Fin n)) (hO₀ : O₀.card = k)
    (i₀ : Fin n) (hi₀ : i₀ ∉ O₀) (π : Fin n ≃ Fin n), ∀ (σ : Instance n) (hσ : ValidInstance σ), ∀ O : Schedule n,
      LazyFeasible k O₀ O σ →
      ENNReal.ofReal (criticalFetch w (run k w O₀ i₀ π σ)) ≤
        ENNReal.ofReal (C₁ * logFactor k) * totalCost w O₀ O σ +
        ENNReal.ofReal (excess k w O₀ O (run k w O₀ i₀ π σ)) +
        ENNReal.ofReal (C₂ * logFactor k * ∑ i, w i) := by sorry

end PagingDelay.PMD
