-- Prove2me | Theorems.Thm_PagingDelay_PMD_proposition_12
-- name    : PagingDelay.PMD.proposition_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:49:12.964405+00:00
-- url     : https://prove2.me/theorems/6b73fca4-b989-4502-a95b-7d6b9e824019
-- title:
--   Proposition 12 — reduction to critical fetch cost
-- statement:
--   Fix the paging parameters, initialization and tie order. Suppose the same constants $\rho,c\ge0$ satisfy $C^{\rm crit}_{\rm fetch}(\sigma)\le\rho\operatorname{Opt}(\sigma)+c$ for every valid instance. Then for every valid instance,
--
--   $$C_{\rm fetch}(\sigma)+C_{\rm delay}(\sigma)\le23\rho\operatorname{Opt}(\sigma)+23c+21\sum_iw_i.$$
--
--   The hypothesis and conclusion both range over all instances; neither constant can depend on the request list. The comparator is the true infimum over all offline schedules.
--
--   Differences from the source:
--   - encoding: finite pages, continuous time, finite requests and instantaneous cache walks → Fin n pages, real times, finite request and event lists, and ENNReal costs; reason: same instances; positive weights reduce every finite-cost offline schedule to finitely many fetches without increasing cost
--   - reading: any tie-breaking rule suffices → all page orders π and all designated initial pages i₀ outside O₀; reason: an arbitrary order resolves simultaneous critical times and equal effective deadlines; no order is fixed
--   - encoding: Algorithm 1 with instantaneous services and eventual service → explicit transition recursion with |σ|+1 next-event iterations, transient states, optional infima and zero-denominator guards; reason: each critical service serves a pending request, so there are at most |σ|; the guards only totalize undefined inputs, and Lemma 2 states full service rather than assuming it
--   - encoding: the first nonnegative hitting time |λ| and natural logarithm L → guarded real infimum and L = log(2k+1); reason: on the stated valid domain the hitting set is nonempty, bounded below and closed; k≥1 makes L positive
-- source:
--   Julian Born, Yann Disser, Linda Thelen, Tight weighted paging with delay via mirror descent, STOC 2027 submission #453 (October 2026), Proposition 12 — reduction to critical fetch cost, p. 16. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/453.pdf

import Definitions.Def_PagingDelay_PMD_Algorithm

namespace PagingDelay.PMD
open scoped BigOperators

/-- Julian Born, Yann Disser, Linda Thelen, Tight weighted paging with delay via mirror descent, STOC 2027 submission #453 (October 2026), Proposition 12 — reduction to critical fetch cost, p. 16. -/
theorem proposition_12 (n k : ℕ) (hk : 1 ≤ k) (hkn : k < n)
    (w : Fin n → ℝ) (hw : PMDWeights w)
    (O₀ : Finset (Fin n)) (hO₀ : O₀.card = k)
    (i₀ : Fin n) (hi₀ : i₀ ∉ O₀) (π : Fin n ≃ Fin n)
    (ρ c : ℝ) (hρ : 0 ≤ ρ) (hc : 0 ≤ c)
    (hbound : ∀ σ : Instance n, ValidInstance σ →
      ENNReal.ofReal (criticalFetch w (run k w O₀ i₀ π σ)) ≤
        ENNReal.ofReal ρ * optimum k w O₀ σ + ENNReal.ofReal c) :
    ∀ σ : Instance n, ValidInstance σ →
      ENNReal.ofReal (fractionalFetch w (run k w O₀ i₀ π σ)) +
        fractionalDelay k (run k w O₀ i₀ π σ) σ ≤
      ENNReal.ofReal (23 * ρ) * optimum k w O₀ σ +
        ENNReal.ofReal (23 * c + 21 * ∑ i, w i) := by sorry

end PagingDelay.PMD
