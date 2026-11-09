-- Prove2me | Theorems.Thm_PagingDelay_PMD_lemma_5
-- name    : PagingDelay.PMD.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:48:27.995185+00:00
-- url     : https://prove2.me/theorems/a763df31-1cb1-4efa-88a9-6aa2b0aba01d
-- title:
--   Lemma 5 — path length versus weighted eviction
-- statement:
--   For every state $x\in[\delta,1]^n$ with $\sum_i x_i=n-k$ and every page $p$, the closed mirror-descent path satisfies
--
--   $$|\lambda_{x\to p}|\le3\operatorname{EV}(\lambda_{x\to p}).$$
--
--   Weighted eviction integrates the positive antimass derivatives with page weights. This is a statement about the explicit path and requires no PMD execution.
--
--   Differences from the source:
--   - encoding: pages indexed by 1 through n → pages indexed by Fin n; reason: a bijective reindexing of the same finite page universe
--   - encoding: the first nonnegative hitting time |λ| and natural logarithm L → guarded real infimum and L = log(2k+1); reason: on the stated valid domain the hitting set is nonempty, bounded below and closed; k≥1 makes L positive
--   - encoding: piecewise differentiable path integrated through finitely many kinks → interval integral using deriv, zero at nondifferentiable points; reason: the integrand is bounded and piecewise continuous on the finite path interval; changing finitely many values leaves the integral unchanged
-- source:
--   Julian Born, Yann Disser, Linda Thelen, Tight weighted paging with delay via mirror descent, STOC 2027 submission #453 (October 2026), Lemma 5 — path length versus weighted eviction, p. 11. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/453.pdf

import Definitions.Def_PagingDelay_PMD_Path

namespace PagingDelay.PMD
open scoped BigOperators

/-- Julian Born, Yann Disser, Linda Thelen, Tight weighted paging with delay via mirror descent, STOC 2027 submission #453 (October 2026), Lemma 5 — path length versus weighted eviction, p. 11. -/
theorem lemma_5 (n k : ℕ) (hk : 1 ≤ k) (hkn : k < n)
    (w : Fin n → ℝ) (hw : PMDWeights w)
    (x : Fin n → ℝ) (hx : StateValid k x)
    (p : Fin n) :
    pathLength k w x p ≤ 3 * weightedEviction k w x p := by sorry

end PagingDelay.PMD
