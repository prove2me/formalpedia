-- Prove2me | Theorems.Thm_PagingDelay_PMD_theorem_1
-- name    : PagingDelay.PMD.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:47:39.279171+00:00
-- url     : https://prove2.me/theorems/6bb4b932-8a64-4117-b85c-21e4bce7f0c6
-- title:
--   Theorem 1 — O(log k)-competitive weighted paging with delay
-- statement:
--   There is an absolute constant $C>0$ such that, for every number $n$ of pages, every $1\le k\le n$, every positive real weight vector $w$, and every initial cache $O_0$ of exactly $k$ pages, there are a clairvoyant randomized online algorithm $A$ starting at $O_0$ and a constant $c\ge0$ with
--
--   $$\mathbb E[\operatorname{cost}(A,\sigma)]\le C\log(2k+1)\operatorname{Opt}(\sigma)+c\qquad\text{for every valid instance }\sigma.$$
--
--   The probability space, algorithm and additive constant are fixed before the request instance. The optimum ranges over all offline schedules. Requests have arbitrary continuous, nondecreasing, unbounded delay functions, zero at zero. Duplicate requests and simultaneous arrivals are permitted. The full-cache case $k=n$ is included. This is the complete competitive existence claim, without a fractional or dyadic restriction.
--
--   Differences from the source:
--   - encoding: finite pages, continuous time, finite requests and instantaneous cache walks → Fin n pages, real times, finite request and event lists, and ENNReal costs; reason: same instances; positive weights reduce every finite-cost offline schedule to finitely many fetches without increasing cost
--   - reading: O(log k), including cache size one → C log(2k+1) with an absolute C; reason: the paper proves L=log(2k+1); this is comparable to 1+log k for every k≥1, and avoids a zero ratio at k=1
--   - encoding: randomized algorithms and their expected costs → probability measures, per-seed online maps and measurable total, fetch and delay cost observables; reason: the usual measurability convention for random costs is explicit; expectations are integrals of random variables rather than arbitrary lower integrals
-- source:
--   Julian Born, Yann Disser, Linda Thelen, Tight weighted paging with delay via mirror descent, STOC 2027 submission #453 (October 2026), Theorem 1 — O(log k)-competitive weighted paging with delay, p. 2. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/453.pdf

import Definitions.Def_PagingDelay_PMD_Model

namespace PagingDelay.PMD
open scoped BigOperators

/-- Julian Born, Yann Disser, Linda Thelen, Tight weighted paging with delay via mirror descent, STOC 2027 submission #453 (October 2026), Theorem 1 — O(log k)-competitive weighted paging with delay, p. 2. -/
theorem theorem_1  :
    ∃ C : ℝ, 0 < C ∧ ∀ (n k : ℕ), 1 ≤ k → k ≤ n →
      ∀ (w : Fin n → ℝ), (∀ i, 0 < w i) →
      ∀ (O₀ : Finset (Fin n)), O₀.card = k →
      ∃ (A : RandomizedAlgorithm n k w O₀) (c : ℝ), 0 ≤ c ∧
      ∀ (σ : Instance n), ValidInstance σ →
      expectedCost A σ ≤ ENNReal.ofReal (C * Real.log (2 * (k : ℝ) + 1)) * optimum k w O₀ σ +
        ENNReal.ofReal c := by sorry

end PagingDelay.PMD
