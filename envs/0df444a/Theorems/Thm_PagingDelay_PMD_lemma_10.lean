-- Prove2me | Theorems.Thm_PagingDelay_PMD_lemma_10
-- name    : PagingDelay.PMD.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:48:43.136989+00:00
-- url     : https://prove2.me/theorems/b562b96a-beb3-42a9-9487-c7a5302ea166
-- title:
--   Lemma 10 — triangle inequality for critical length
-- statement:
--   Let $x$ be a valid state just before a critical service to $p$, and let $\widetilde x=\lambda_{x\to p}(|\lambda_{x\to p}|)$. For any other page $q$ with $x_q>\delta$,
--
--   $$|\lambda_{x\to q}|\le |\lambda_{x\to p}|+|\lambda_{\widetilde x\to q}|.$$
--
--   The post-service state is computed from the path, rather than quantified independently.
--
--   Differences from the source:
--   - encoding: pages indexed by 1 through n → pages indexed by Fin n; reason: a bijective reindexing of the same finite page universe
--   - encoding: the first nonnegative hitting time |λ| and natural logarithm L → guarded real infimum and L = log(2k+1); reason: on the stated valid domain the hitting set is nonempty, bounded below and closed; k≥1 makes L positive
-- source:
--   Julian Born, Yann Disser, Linda Thelen, Tight weighted paging with delay via mirror descent, STOC 2027 submission #453 (October 2026), Lemma 10 — triangle inequality for critical length, p. 14. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/453.pdf

import Definitions.Def_PagingDelay_PMD_Path

namespace PagingDelay.PMD
open scoped BigOperators

/-- Julian Born, Yann Disser, Linda Thelen, Tight weighted paging with delay via mirror descent, STOC 2027 submission #453 (October 2026), Lemma 10 — triangle inequality for critical length, p. 14. -/
theorem lemma_10 (n k : ℕ) (hk : 1 ≤ k) (hkn : k < n)
    (w : Fin n → ℝ) (hw : PMDWeights w)
    (x : Fin n → ℝ) (hx : StateValid k x)
    (p q : Fin n) (hp : delta k < x p) (hpq : q ≠ p) (hq : delta k < x q) :
    pathLength k w x q ≤ pathLength k w x p + pathLength k w (pathEnd k w x p) q := by sorry

end PagingDelay.PMD
