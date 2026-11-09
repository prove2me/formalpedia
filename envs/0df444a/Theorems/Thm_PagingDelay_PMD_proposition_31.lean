-- Prove2me | Theorems.Thm_PagingDelay_PMD_proposition_31
-- name    : PagingDelay.PMD.proposition_31
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:49:35.723383+00:00
-- url     : https://prove2.me/theorems/5d2ef558-5150-4708-810a-39f15d10aec8
-- title:
--   Proposition 31 — integral online conversion of PMD
-- statement:
--   There is an absolute positive constant $C$ such that, for every PMD parameter setting, initialization and tie order, there exists a clairvoyant randomized online integral algorithm $A$ starting at $O_0$. For every valid instance, it serves all requests almost surely and satisfies
--
--   $$\mathbb E[\operatorname{fetch}(A,\sigma)]\le C\left(C_{\rm fetch}(\sigma)+\sum_iw_i\right),\qquad
--   \mathbb E[\operatorname{delay}(A,\sigma)]\le3C_{\rm delay}(\sigma).$$
--
--   The fractional quantities refer to PMD on that same instance. The algorithm and its probability space are chosen before the instance; per-seed online-ness and measurable cost are part of the algorithm interface. All three conclusions are retained.
--
--   Differences from the source:
--   - encoding: finite pages, continuous time, finite requests and instantaneous cache walks → Fin n pages, real times, finite request and event lists, and ENNReal costs; reason: same instances; positive weights reduce every finite-cost offline schedule to finitely many fetches without increasing cost
--   - reading: any tie-breaking rule suffices → all page orders π and all designated initial pages i₀ outside O₀; reason: an arbitrary order resolves simultaneous critical times and equal effective deadlines; no order is fixed
--   - encoding: Algorithm 1 with instantaneous services and eventual service → explicit transition recursion with |σ|+1 next-event iterations, transient states, optional infima and zero-denominator guards; reason: each critical service serves a pending request, so there are at most |σ|; the guards only totalize undefined inputs, and Lemma 2 states full service rather than assuming it
--   - encoding: the first nonnegative hitting time |λ| and natural logarithm L → guarded real infimum and L = log(2k+1); reason: on the stated valid domain the hitting set is nonempty, bounded below and closed; k≥1 makes L positive
--   - encoding: randomized algorithms and their expected costs → probability measures, per-seed online maps and measurable total, fetch and delay cost observables; reason: the usual measurability convention for random costs is explicit; expectations are integrals of random variables rather than arbitrary lower integrals
-- source:
--   Julian Born, Yann Disser, Linda Thelen, Tight weighted paging with delay via mirror descent, STOC 2027 submission #453 (October 2026), Proposition 31 — integral online conversion of PMD, p. 23. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/453.pdf

import Definitions.Def_PagingDelay_PMD_Algorithm

namespace PagingDelay.PMD
open scoped BigOperators

/-- Julian Born, Yann Disser, Linda Thelen, Tight weighted paging with delay via mirror descent, STOC 2027 submission #453 (October 2026), Proposition 31 — integral online conversion of PMD, p. 23. -/
theorem proposition_31  :
    ∃ C : ℝ, 0 < C ∧ ∀ (n k : ℕ) (hk : 1 ≤ k) (hkn : k < n)
    (w : Fin n → ℝ) (hw : PMDWeights w)
    (O₀ : Finset (Fin n)) (hO₀ : O₀.card = k)
    (i₀ : Fin n) (hi₀ : i₀ ∉ O₀) (π : Fin n ≃ Fin n),
      ∃ A : RandomizedAlgorithm n k w O₀,
      ∀ (σ : Instance n) (hσ : ValidInstance σ),
      ServesAlmostSurely A σ ∧
      expectedFetch A σ ≤ ENNReal.ofReal (C * (fractionalFetch w (run k w O₀ i₀ π σ) + ∑ i, w i)) ∧
      expectedDelay A σ ≤ 3 * fractionalDelay k (run k w O₀ i₀ π σ) σ := by sorry

end PagingDelay.PMD
