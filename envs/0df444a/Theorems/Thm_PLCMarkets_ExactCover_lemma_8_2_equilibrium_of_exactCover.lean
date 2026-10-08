-- Prove2me | Theorems.Thm_PLCMarkets_ExactCover_lemma_8_2_equilibrium_of_exactCover
-- name    : PLCMarkets.ExactCover.lemma_8_2_equilibrium_of_exactCover
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T01:05:00.697333+00:00
-- url     : https://prove2.me/theorems/3ab7e81b-2b87-4efc-a1ea-a1172e1e3c1b
-- title:
--   LEMMA 8.2 (Arrow–Debreu half) — an exact cover yields an equilibrium of $D(\mathcal C)$
-- statement:
--   Let $n>35$ be a multiple of $3$ and let $\mathcal C=(C_1,\dots,C_n)$ be a family of $3$-element subsets of $X=\{x_1,\dots,x_n\}$ whose union is $X$. If $\mathcal C$ has an exact cover, then the Arrow–Debreu market $D(\mathcal C)$ of §8 has a price equilibrium:
--
--   $$
--   \mathcal C\ \text{has an exact cover}\ \Longrightarrow\ \exists\,p\ \text{a price equilibrium of}\ D(\mathcal C).
--   $$
--
--   This is the "exact cover $\Rightarrow$ equilibrium" direction of the reduction from X3C that proves the NP-hardness in Theorem 8.1.
--
--   **Formalization Note.** The paper's Lemma 8.2 asserts the conclusion for both the Arrow–Debreu market $D$ and the Fisher market $F$; this is its Arrow–Debreu half. The hypotheses $3\mid n$, $n>35$ and $\bigcup_i C_i=X$ are the standing assumptions of §8 (p. 10:19), carried by every theorem of this mission.
-- source:
--   Vazirani and Yannakakis, Market Equilibrium under Separable, Piecewise-Linear, Concave Utilities, J. ACM 58(3), Article 10, 2011, p. 10:20, LEMMA 8.2 (Arrow–Debreu half); standing assumptions p. 10:19

import Mathlib
import Definitions.Def_PLCMarkets_ExactCover_X3C
import Definitions.Def_PLCMarkets_ExactCover_MarketD

namespace PLCMarkets.ExactCover

theorem lemma_8_2_equilibrium_of_exactCover (n : ℕ) (C : Fin n → Finset (Fin n))
    (hcard : ∀ i, (C i).card = 3) (hdiv : 3 ∣ n) (hn : 35 < n)
    (hcover : ∀ x : Fin n, ∃ i, x ∈ C i)
    (hC : HasExactCover C) :
    ∃ p : Good n → ℝ, (marketD C).IsEquilibrium p := by sorry

end PLCMarkets.ExactCover
