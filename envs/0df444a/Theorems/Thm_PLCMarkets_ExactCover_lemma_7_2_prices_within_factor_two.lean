-- Prove2me | Theorems.Thm_PLCMarkets_ExactCover_lemma_7_2_prices_within_factor_two
-- name    : PLCMarkets.ExactCover.lemma_7_2_prices_within_factor_two
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T01:05:42.584546+00:00
-- url     : https://prove2.me/theorems/c9e55ab3-0736-4ec6-a509-474fcdf8087d
-- title:
--   LEMMA 7.2 (as applied in the proof of LEMMA 8.3) — prices of an $n^{-5}$-equilibrium of $D(\mathcal C)$ are positive and within a factor 2
-- statement:
--   Let $n>35$ be a multiple of $3$ and let $\mathcal C=(C_1,\dots,C_n)$ be a family of $3$-element subsets of $X=\{x_1,\dots,x_n\}$ whose union is $X$. If $p$ is an $\epsilon$-approximate market equilibrium of the Arrow–Debreu market $D(\mathcal C)$ with $\epsilon=n^{-5}$, then all prices are positive and within a factor $2$ of each other:
--
--   $$
--   p(j)>0\quad\text{and}\quad p(j)\le 2\,p(k)\qquad\text{for all goods } j,k .
--   $$
--
--   This is the price-regulation property enforced by agent $0$, whose endowment dominates the market; the proof of Lemma 8.3 starts from it.
--
--   **Formalization Note.** Lemma 7.2 of the paper (p. 10:17) reads: "In any 0.9-approximate price equilibrium for this Fisher market instance F, the prices of all the goods are positive and are within a factor 2 of each other." It is stated for the Fisher instance of §7, which is built on a black-box market of Chen et al.; the proof of Lemma 8.3 (p. 10:21) applies it to the §8 markets with $\epsilon=n^{-5}$. This item states that application, for the market $D(\mathcal C)$, not the §7 lemma.
-- source:
--   Vazirani and Yannakakis, Market Equilibrium under Separable, Piecewise-Linear, Concave Utilities, J. ACM 58(3), Article 10, 2011, p. 10:17, LEMMA 7.2, as invoked on p. 10:21 in the proof of LEMMA 8.3

import Mathlib
import Definitions.Def_PLCMarkets_ExactCover_X3C
import Definitions.Def_PLCMarkets_ExactCover_MarketD

namespace PLCMarkets.ExactCover

theorem lemma_7_2_prices_within_factor_two (n : ℕ) (C : Fin n → Finset (Fin n))
    (hcard : ∀ i, (C i).card = 3) (hdiv : 3 ∣ n) (hn : 35 < n)
    (hcover : ∀ x : Fin n, ∃ i, x ∈ C i)
    (p : Good n → ℝ)
    (hp : (marketD C).IsApproxEquilibrium (((n : ℝ) ^ 5)⁻¹) p) :
    (∀ j, 0 < p j) ∧ ∀ j k, p j ≤ 2 * p k := by sorry

end PLCMarkets.ExactCover
