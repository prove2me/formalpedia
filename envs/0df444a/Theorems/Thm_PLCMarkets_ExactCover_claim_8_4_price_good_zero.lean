-- Prove2me | Theorems.Thm_PLCMarkets_ExactCover_claim_8_4_price_good_zero
-- name    : PLCMarkets.ExactCover.claim_8_4_price_good_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T01:10:16.468494+00:00
-- url     : https://prove2.me/theorems/b7427d57-3efa-47b6-bcbf-9159a8659093
-- title:
--   CLAIM 8.4 — in an $n^{-5}$-equilibrium of $D(\mathcal C)$, good 0 has price $2p_m$
-- statement:
--   Let $n>35$ be a multiple of $3$ and let $\mathcal C=(C_1,\dots,C_n)$ be a family of $3$-element subsets of $X=\{x_1,\dots,x_n\}$ whose union is $X$. Let $p$ be an $n^{-5}$-approximate market equilibrium of the Arrow–Debreu market $D(\mathcal C)$, and let $p_m=\min_j p(j)$ be the minimum price. Then good $0$ has twice the minimum price:
--
--   $$
--   p(0)=2\,p_m .
--   $$
--
--   This is the first of the four claims from which the proof of Lemma 8.3 extracts an exact cover.
-- source:
--   Vazirani and Yannakakis, Market Equilibrium under Separable, Piecewise-Linear, Concave Utilities, J. ACM 58(3), Article 10, 2011, p. 10:22, CLAIM 8.4 (in the proof of LEMMA 8.3)

import Mathlib
import Definitions.Def_PLCMarkets_ExactCover_X3C
import Definitions.Def_PLCMarkets_ExactCover_MarketD

namespace PLCMarkets.ExactCover

theorem claim_8_4_price_good_zero (n : ℕ) (C : Fin n → Finset (Fin n))
    (hcard : ∀ i, (C i).card = 3) (hdiv : 3 ∣ n) (hn : 35 < n)
    (hcover : ∀ x : Fin n, ∃ i, x ∈ C i)
    (p : Good n → ℝ)
    (hp : (marketD C).IsApproxEquilibrium (((n : ℝ) ^ 5)⁻¹) p) :
    p Good.zero = 2 * minPrice p := by sorry

end PLCMarkets.ExactCover
