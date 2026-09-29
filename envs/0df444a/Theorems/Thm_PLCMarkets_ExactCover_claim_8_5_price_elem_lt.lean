-- Prove2me | Theorems.Thm_PLCMarkets_ExactCover_claim_8_5_price_elem_lt
-- name    : PLCMarkets.ExactCover.claim_8_5_price_elem_lt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T01:11:02.474487+00:00
-- url     : https://prove2.me/theorems/61e611ad-57fa-450f-844c-892ac78bd146
-- title:
--   CLAIM 8.5 — in an $n^{-5}$-equilibrium of $D(\mathcal C)$, every good $x_j$ costs less than $2p_m$
-- statement:
--   Let $n>35$ be a multiple of $3$ and let $\mathcal C=(C_1,\dots,C_n)$ be a family of $3$-element subsets of $X=\{x_1,\dots,x_n\}$ whose union is $X$. Let $p$ be an $n^{-5}$-approximate market equilibrium of the Arrow–Debreu market $D(\mathcal C)$, and let $p_m=\min_j p(j)$. Then every element good is priced strictly below $2p_m$:
--
--   $$
--   p(x_j)<2\,p_m\qquad\text{for all } x_j\in X .
--   $$
--
--   Claim 8.7 uses this bound to show that the sets of $S$ are disjoint.
-- source:
--   Vazirani and Yannakakis, Market Equilibrium under Separable, Piecewise-Linear, Concave Utilities, J. ACM 58(3), Article 10, 2011, p. 10:22, CLAIM 8.5 (in the proof of LEMMA 8.3)

import Mathlib
import Definitions.Def_PLCMarkets_ExactCover_X3C
import Definitions.Def_PLCMarkets_ExactCover_MarketD

namespace PLCMarkets.ExactCover

theorem claim_8_5_price_elem_lt (n : ℕ) (C : Fin n → Finset (Fin n))
    (hcard : ∀ i, (C i).card = 3) (hdiv : 3 ∣ n) (hn : 35 < n)
    (hcover : ∀ x : Fin n, ∃ i, x ∈ C i)
    (p : Good n → ℝ)
    (hp : (marketD C).IsApproxEquilibrium (((n : ℝ) ^ 5)⁻¹) p) :
    ∀ j : Fin n, p (Good.elem j) < 2 * minPrice p := by sorry

end PLCMarkets.ExactCover
