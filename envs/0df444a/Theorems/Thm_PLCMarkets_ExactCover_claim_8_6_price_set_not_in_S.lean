-- Prove2me | Theorems.Thm_PLCMarkets_ExactCover_claim_8_6_price_set_not_in_S
-- name    : PLCMarkets.ExactCover.claim_8_6_price_set_not_in_S
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T01:11:48.485355+00:00
-- url     : https://prove2.me/theorems/6b048a8a-f77b-4481-ae4e-56696f1d4f32
-- title:
--   CLAIM 8.6 — in an $n^{-5}$-equilibrium of $D(\mathcal C)$, $C_i\notin S$ implies $p(C_i)=p_m$
-- statement:
--   Let $n>35$ be a multiple of $3$ and let $\mathcal C=(C_1,\dots,C_n)$ be a family of $3$-element subsets of $X=\{x_1,\dots,x_n\}$ whose union is $X$. Let $p$ be an $n^{-5}$-approximate market equilibrium of the Arrow–Debreu market $D(\mathcal C)$, let $p_m=\min_j p(j)$, and let $S$ be the set of indices $i$ with $p(C_i)\ge p_m+\tfrac16\sum_{x_j\in C_i}p(x_j)$. Then
--
--   $$
--   i\notin S\ \Longrightarrow\ p(C_i)=p_m .
--   $$
--
--   Together with Claims 8.4 and 8.7 this pins down the prices the final counting argument of Lemma 8.3 uses.
-- source:
--   Vazirani and Yannakakis, Market Equilibrium under Separable, Piecewise-Linear, Concave Utilities, J. ACM 58(3), Article 10, 2011, p. 10:22, definition of S and CLAIM 8.6 (in the proof of LEMMA 8.3)

import Mathlib
import Definitions.Def_PLCMarkets_ExactCover_X3C
import Definitions.Def_PLCMarkets_ExactCover_MarketD

namespace PLCMarkets.ExactCover

theorem claim_8_6_price_set_not_in_S (n : ℕ) (C : Fin n → Finset (Fin n))
    (hcard : ∀ i, (C i).card = 3) (hdiv : 3 ∣ n) (hn : 35 < n)
    (hcover : ∀ x : Fin n, ∃ i, x ∈ C i)
    (p : Good n → ℝ)
    (hp : (marketD C).IsApproxEquilibrium (((n : ℝ) ^ 5)⁻¹) p) :
    ∀ i : Fin n, i ∉ coverSet C p → p (Good.set i) = minPrice p := by sorry

end PLCMarkets.ExactCover
