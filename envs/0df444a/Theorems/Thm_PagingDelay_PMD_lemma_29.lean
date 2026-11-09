-- Prove2me | Theorems.Thm_PagingDelay_PMD_lemma_29
-- name    : PagingDelay.PMD.lemma_29
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:48:22.675883+00:00
-- url     : https://prove2.me/theorems/2e1df931-d9a4-4dea-badf-5f37c7429db7
-- title:
--   Lemma 29 — lightest weights of offline period caches
-- statement:
--   For any lazy feasible offline schedule $O$, let $O_j$ be its cache after the positive-cost walk at the $j$th distinct update time. Excluding the initial period,
--
--   $$\sum_{j\ge1}w_{\min}(O_j)\le\operatorname{cost}(O).$$
--
--   Each walk time is counted once, even if it contains several swaps. The empty list of walks gives the empty sum.
--
--   Differences from the source:
--   - encoding: finite pages, continuous time, finite requests and instantaneous cache walks → Fin n pages, real times, finite request and event lists, and ENNReal costs; reason: same instances; positive weights reduce every finite-cost offline schedule to finitely many fetches without increasing cost
--   - generalization: an optimal lazy offline schedule Opt → every lazy feasible offline schedule O, with cost(O) on the right; reason: the source proofs use only laziness and service of every request; an optimal lazy schedule is one such comparator
-- source:
--   Julian Born, Yann Disser, Linda Thelen, Tight weighted paging with delay via mirror descent, STOC 2027 submission #453 (October 2026), Lemma 29 — lightest weights of offline period caches, p. 22. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/453.pdf

import Definitions.Def_PagingDelay_PMD_Path

namespace PagingDelay.PMD
open scoped BigOperators

/-- Julian Born, Yann Disser, Linda Thelen, Tight weighted paging with delay via mirror descent, STOC 2027 submission #453 (October 2026), Lemma 29 — lightest weights of offline period caches, p. 22. -/
theorem lemma_29 (n k : ℕ) (hk : 1 ≤ k) (hkn : k < n)
    (w : Fin n → ℝ) (hw : PMDWeights w)
    (O₀ : Finset (Fin n)) (hO₀ : O₀.card = k)
    (σ : Instance n) (hσ : ValidInstance σ) (O : Schedule n)
    (hO : LazyFeasible k O₀ O σ) :
    ENNReal.ofReal (((periodCaches O₀ O).map (minWeight w)).sum) ≤ totalCost w O₀ O σ := by sorry

end PagingDelay.PMD
