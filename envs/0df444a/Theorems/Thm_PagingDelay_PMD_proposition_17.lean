-- Prove2me | Theorems.Thm_PagingDelay_PMD_proposition_17
-- name    : PagingDelay.PMD.proposition_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:48:23.669674+00:00
-- url     : https://prove2.me/theorems/5946e407-b953-4bb0-b1bc-71c548102dc8
-- title:
--   Proposition 17 — hit and miss potential changes
-- statement:
--   For a critical path $\lambda_{x\to p}$, keep the offline cache $O$ fixed with exactly $k$ pages and write $\Delta D=D(O\Vert\lambda(|\lambda|))-D(O\Vert x)$. Both cases hold:
--
--   $$p\in O\implies\Delta D\le-\operatorname{fetch}(\lambda),\qquad
--   p\notin O\implies\Delta D\le2Lw_p+\operatorname{Exc}(\lambda,O).$$
--
--   The excess is the sum of the path's level-$W$ lengths for $w_p\le W<w_{\min}(O)$, with coefficient exactly one.
--
--   Differences from the source:
--   - encoding: pages indexed by 1 through n → pages indexed by Fin n; reason: a bijective reindexing of the same finite page universe
--   - encoding: the first nonnegative hitting time |λ| and natural logarithm L → guarded real infimum and L = log(2k+1); reason: on the stated valid domain the hitting set is nonempty, bounded below and closed; k≥1 makes L positive
--   - generalization: a positive-length critical service with x_p>δ → all valid states, also the zero-length boundary x_p=δ; reason: at the added boundary pathLength, ΔD, fetch and excess are zero, so both source inequalities still hold
-- source:
--   Julian Born, Yann Disser, Linda Thelen, Tight weighted paging with delay via mirror descent, STOC 2027 submission #453 (October 2026), Proposition 17 — hit and miss potential changes, p. 17. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/453.pdf

import Definitions.Def_PagingDelay_PMD_Path

namespace PagingDelay.PMD
open scoped BigOperators

/-- Julian Born, Yann Disser, Linda Thelen, Tight weighted paging with delay via mirror descent, STOC 2027 submission #453 (October 2026), Proposition 17 — hit and miss potential changes, p. 17. -/
theorem proposition_17 (n k : ℕ) (hk : 1 ≤ k) (hkn : k < n)
    (w : Fin n → ℝ) (hw : PMDWeights w)
    (x : Fin n → ℝ) (hx : StateValid k x)
    (p : Fin n) (O : Finset (Fin n)) (hO : O.card = k) :
    let Δ := potential w O (pathEnd k w x p) - potential w O x
    (p ∈ O → Δ ≤ -pathFetch k w x p) ∧
    (p ∉ O → Δ ≤ 2 * logFactor k * w p + serviceExcess k w x p O) := by sorry

end PagingDelay.PMD
