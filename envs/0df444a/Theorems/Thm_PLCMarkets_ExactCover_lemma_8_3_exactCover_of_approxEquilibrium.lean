-- Prove2me | Theorems.Thm_PLCMarkets_ExactCover_lemma_8_3_exactCover_of_approxEquilibrium
-- name    : PLCMarkets.ExactCover.lemma_8_3_exactCover_of_approxEquilibrium
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T01:12:57.351308+00:00
-- url     : https://prove2.me/theorems/cadc30cb-0110-47ae-8aa1-f1b16451bdc5
-- title:
--   LEMMA 8.3 (Arrow–Debreu half) — an equilibrium, or an $n^{-5}$-equilibrium, of $D(\mathcal C)$ yields an exact cover
-- statement:
--   Let $n>35$ be a multiple of $3$ and let $\mathcal C=(C_1,\dots,C_n)$ be a family of $3$-element subsets of $X=\{x_1,\dots,x_n\}$ whose union is $X$. If the Arrow–Debreu market $D(\mathcal C)$ has a price equilibrium, or even an $\epsilon$-approximate market equilibrium with $\epsilon=n^{-5}$, then $\mathcal C$ has an exact cover:
--
--   $$
--   \big(\exists\,p\ \text{equilibrium of}\ D(\mathcal C)\big)\ \vee\ \big(\exists\,p\ \ n^{-5}\text{-approximate equilibrium of}\ D(\mathcal C)\big)\ \Longrightarrow\ \mathcal C\ \text{has an exact cover}.
--   $$
--
--   This is the "equilibrium $\Rightarrow$ exact cover" direction of the reduction behind Theorem 8.1, in the strengthened form that also covers approximate equilibria.
--
--   **Formalization Note.** The paper's Lemma 8.3 is stated for the Fisher market $F$ or the Arrow–Debreu market $D$; this is its Arrow–Debreu half, the one the paper writes out ("For concreteness, we give the arguments in the following for the Arrow–Debreu case", p. 10:21).
-- source:
--   Vazirani and Yannakakis, Market Equilibrium under Separable, Piecewise-Linear, Concave Utilities, J. ACM 58(3), Article 10, 2011, p. 10:21, LEMMA 8.3 (Arrow–Debreu half); proof pp. 10:21-10:23

import Mathlib
import Definitions.Def_PLCMarkets_ExactCover_X3C
import Definitions.Def_PLCMarkets_ExactCover_MarketD

namespace PLCMarkets.ExactCover

theorem lemma_8_3_exactCover_of_approxEquilibrium (n : ℕ) (C : Fin n → Finset (Fin n))
    (hcard : ∀ i, (C i).card = 3) (hdiv : 3 ∣ n) (hn : 35 < n)
    (hcover : ∀ x : Fin n, ∃ i, x ∈ C i)
    (h : (∃ p : Good n → ℝ, (marketD C).IsEquilibrium p) ∨
      (∃ p : Good n → ℝ, (marketD C).IsApproxEquilibrium (((n : ℝ) ^ 5)⁻¹) p)) :
    HasExactCover C := by sorry

end PLCMarkets.ExactCover
