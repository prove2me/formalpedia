-- Prove2me | Theorems.Thm_PagingDelay_PMD_corollary_33
-- name    : PagingDelay.PMD.corollary_33
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:49:41.790403+00:00
-- url     : https://prove2.me/theorems/eeafadc8-9428-4f7e-bdeb-6ee0e111136d
-- title:
--   Corollary 33 — online rounding with exact marginals
-- statement:
--   For dyadic page weights and an initial cache $O_0$ of exactly $k$ pages, there is one randomized rounding rule defined on all valid fractional cache histories, chosen before the history is supplied. Write $C^{(\nu)}=R(y^{(0)},\ldots,y^{(\nu)})$. The rule depends only on this prefix and its seed; every membership event is measurable. It satisfies $C^{(0)}=O_0$ and $|C^{(\nu)}|=k$, and
--
--   $$\Pr[i\in C^{(\nu)}]=y_i^{(\nu)},\qquad
--   \mathbb E\!\left[\sum_{i\in C^{(\nu+1)}\setminus C^{(\nu)}}w_i\right]\le5\sum_iw_i|y_i^{(\nu+1)}-y_i^{(\nu)}|.$$
--
--   This is the rounding theorem to be proved; no BBN07 assumption is made.
--
--   Differences from the source:
--   - encoding: pages indexed by 1 through n → pages indexed by Fin n; reason: a bijective reindexing of the same finite page universe
--   - encoding: online random cache choices for vectors arriving one at a time → one probability space and a measurable prefix map R, selected before every finite history; reason: the full random tape is the seed; a prefix map cannot depend on future vectors, and its jointly defined outputs retain transition correlations
-- source:
--   Julian Born, Yann Disser, Linda Thelen, Tight weighted paging with delay via mirror descent, STOC 2027 submission #453 (October 2026), Corollary 33 — online rounding with exact marginals, p. 26. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/453.pdf

import Definitions.Def_PagingDelay_PMD_Rounding

namespace PagingDelay.PMD
open scoped BigOperators

/-- Julian Born, Yann Disser, Linda Thelen, Tight weighted paging with delay via mirror descent, STOC 2027 submission #453 (October 2026), Corollary 33 — online rounding with exact marginals, p. 26. -/
theorem corollary_33 (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n)
    (w : Fin n → ℝ) (hw : DyadicWeights w)
    (O₀ : Finset (Fin n)) (hO₀ : O₀.card = k) :
    ∃ R : OnlineRounding n,
      (∀ ω, R.choose ω [indicator O₀] = O₀) ∧
      (∀ ys, CacheHistory k O₀ ys →
        (∀ ω, (R.choose ω ys).card = k) ∧
        (∀ i, roundingMarginal R ys i = ENNReal.ofReal (ys.getLastD (indicator O₀) i)) ∧
        (∀ y, FractionalCache k y → roundingFetch w R ys y ≤
          ENNReal.ofReal (5 * ∑ i, w i * |y i - ys.getLastD (indicator O₀) i|))) := by sorry

end PagingDelay.PMD
