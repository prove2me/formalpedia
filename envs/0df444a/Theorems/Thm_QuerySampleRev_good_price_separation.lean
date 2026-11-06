-- Prove2me | Theorems.Thm_QuerySampleRev_good_price_separation
-- name    : QuerySampleRev.good_price_separation
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:37:05.723029+00:00
-- url     : https://prove2.me/theorems/9966c88e-a972-4a60-8ffe-17311f21dace
-- title:
--   §5.5 (after Lemma 22) — every $(1-\varepsilon)$-optimal price under $F^{(i)}$ lies in $P^{(i)}$
-- statement:
--   Let $c\in[0,1]$, $0<\varepsilon\le1/128$ and $i\in[K]$, and write $R^{(j)}(p)=p\,Q^{(j)}(p)$ for the revenue curve of $F^{(j)}$. Then
--   1. $R^{(i)}(p)=R^{(0)}(p)$ for every price $p\notin P^{(i)}$;
--   2. the base revenue is at most one: $R^{(0)}(p)\le1$ for every $p$;
--   3. $R^{(i)}(m_i)=1+\rho w/a_i$;
--   4. $1+\rho w/a_i=1+2\varepsilon/a_i\ge1+4\varepsilon/3$;
--   5. $(1-\varepsilon)(1+4\varepsilon/3)>1$;
--   6. every price $p$ with $R^{(i)}(p)\ge(1-\varepsilon)\,r^{*(i)}$ lies in $P^{(i)}$.
--
--   Hence a $(1-\varepsilon)$-optimal price under $F^{(i)}$ identifies the changed interval $P^{(i)}$; since the intervals are disjoint, a PAC output distinguishes the hard instances.
--
--   **Formalization Note** Revenue and $r^{*(i)}$ are in $[0,\infty]$.
--
--   Differences from the source:
--   - generalization: prices $p\ge0$ → every real price $p$ (a negative price earns revenue $0$); reason: specializes to the source on $p\ge0$
-- source:
--   Jin, Tang, Wang, Zhang, Query-Sample Tradeoffs for Revenue Maximization (manuscript, sha256 c31ea3d3…), §5.5, paragraph after Lemma 22, p.37 (PDF p.39)

import Mathlib
import Definitions.Def_QuerySampleRev_rStar
import Definitions.Def_QuerySampleRev_hardDist

open MeasureTheory
open scoped ENNReal

namespace QuerySampleRev

/-- **Good-price separation.** Jin, Tang, Wang, Zhang, *Query-Sample Tradeoffs for Revenue Maximization*
(manuscript, sha256 c31ea3d3…), §5.5, after Lemma 22, p.37 (PDF 39): "We next show that a
`(1 − ε)`-optimal price identifies the changed interval. Under `F⁽ⁱ⁾`, revenue outside `P⁽ⁱ⁾` equals the
base revenue, which is at most one, whereas `r_i(m_i) = 1 + ρw/a_i = 1 + 2ε/a_i ≥ 1 + 4ε/3`. Since
`(1 − ε)(1 + 4ε/3) > 1`, every `(1 − ε)`-optimal price under `F⁽ⁱ⁾` belongs to `P⁽ⁱ⁾`."

For `c ∈ [0, 1]`, `0 < ε ≤ 1/128` and `i ∈ [K]`. -/
theorem good_price_separation {c ε : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hε0 : 0 < ε) (hε : ε ≤ 1 / 128) :
    ∀ i ∈ Finset.Icc 1 (numHard ε c),
      (∀ p ∉ priceInterval ε c i, revenue (hardDist ε c i) p = revenue baseDist p) ∧
      (∀ p : ℝ, revenue baseDist p ≤ 1) ∧
      revenue (hardDist ε c i) (mPt ε c i) =
        ENNReal.ofReal (1 + rho ε c * halfWidth ε c / aPt ε c i) ∧
      1 + rho ε c * halfWidth ε c / aPt ε c i = 1 + 2 * ε / aPt ε c i ∧
      1 + 4 * ε / 3 ≤ 1 + 2 * ε / aPt ε c i ∧
      1 < (1 - ε) * (1 + 4 * ε / 3) ∧
      ∀ p : ℝ, ENNReal.ofReal (1 - ε) * rStar (hardDist ε c i) ≤ revenue (hardDist ε c i) p →
        p ∈ priceInterval ε c i := by sorry

end QuerySampleRev
