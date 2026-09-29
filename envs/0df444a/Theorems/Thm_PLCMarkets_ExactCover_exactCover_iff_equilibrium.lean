-- Prove2me | Theorems.Thm_PLCMarkets_ExactCover_exactCover_iff_equilibrium
-- name    : PLCMarkets.ExactCover.exactCover_iff_equilibrium
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T01:13:35.861298+00:00
-- url     : https://prove2.me/theorems/c578ead5-90da-4125-afa5-523e4953298a
-- title:
--   THEOREM 8.1 (reduction, Arrow–Debreu) — an exact 3-cover exists iff $D(\mathcal C)$ has an equilibrium, iff it has an $n^{-5}$-equilibrium
-- statement:
--   Let $n>35$ be a multiple of $3$ and let $\mathcal C=(C_1,\dots,C_n)$ be a family of $3$-element subsets of $X=\{x_1,\dots,x_n\}$ whose union is $X$. Let $D(\mathcal C)$ be the Arrow–Debreu market with separable piecewise-linear concave utilities constructed from $\mathcal C$ in §8. Then
--
--   $$
--   \mathcal C\ \text{has an exact cover}\iff D(\mathcal C)\ \text{has a price equilibrium}\iff D(\mathcal C)\ \text{has an } n^{-5}\text{-approximate market equilibrium}.
--   $$
--
--   This is the mathematical content of the NP-hardness half of Theorem 8.1: the X3C instance has a solution if and only if the constructed market has an equilibrium, and the equivalence survives passing to $n^{-5}$-approximate equilibria. Combined with the polynomial-time computability of $D(\mathcal C)$ and the NP-completeness of X3C, it shows that deciding whether such a market has an (approximate) equilibrium is NP-hard.
--
--   **Formalization Note.** Stated as two equivalences. The hypotheses $3\mid n$, $n>35$ and $\bigcup_i C_i=X$ are the paper's standing "without loss of generality" assumptions of §8 (p. 10:19). The complexity-class statement ("NP-complete"), membership in NP, and the Fisher market $F$ are not part of this statement.
-- source:
--   Vazirani and Yannakakis, Market Equilibrium under Separable, Piecewise-Linear, Concave Utilities, J. ACM 58(3), Article 10, 2011, p. 10:19, §8 (reduction statement), with LEMMA 8.2 (p. 10:20) and LEMMA 8.3 (p. 10:21); THEOREM 8.1 (p. 10:19), hardness half

import Mathlib
import Definitions.Def_PLCMarkets_ExactCover_X3C
import Definitions.Def_PLCMarkets_ExactCover_MarketD

namespace PLCMarkets.ExactCover

theorem exactCover_iff_equilibrium (n : ℕ) (C : Fin n → Finset (Fin n))
    (hcard : ∀ i, (C i).card = 3) (hdiv : 3 ∣ n) (hn : 35 < n)
    (hcover : ∀ x : Fin n, ∃ i, x ∈ C i) :
    (HasExactCover C ↔ ∃ p : Good n → ℝ, (marketD C).IsEquilibrium p) ∧
      (HasExactCover C ↔
        ∃ p : Good n → ℝ, (marketD C).IsApproxEquilibrium (((n : ℝ) ^ 5)⁻¹) p) := by sorry

end PLCMarkets.ExactCover
