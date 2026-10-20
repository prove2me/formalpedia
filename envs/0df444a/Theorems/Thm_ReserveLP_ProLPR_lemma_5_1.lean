-- Prove2me | Theorems.Thm_ReserveLP_ProLPR_lemma_5_1
-- name    : ReserveLP.ProLPR.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:19:22.606603+00:00
-- url     : https://prove2.me/theorems/f9bf5e76-2c07-41cd-9ad5-bce2ceafffb3
-- title:
--   Lemma 5.1, p. 9 — two per-auction tail conditions give a (1 + c)⁻¹-approximation
-- statement:
--   Let $(s^\star,q^\star)$ be an optimal solution of Profile-LP, and let $r^{\mathcal R}$ be the random reserve vector produced by the Pro-LPR rounding, which draws each buyer's reserve independently from $q^\star_{b,\cdot}$. Suppose there is a constant $c>0$ such that, for every auction $a$ and every $t\ge0$,
--
--   $$\sum_{p\in\mathcal P_a,\ \mathrm{Rev}_a(p)\ge t}s^\star_{a,p}-\Pr[\mathrm{Rev}_a(r^{\mathcal R})\ge t]\le0\quad\text{for }t>\beta^{(2)}_a,$$
--
--   $$\sum_{p\in\mathcal P_a,\ \mathrm{Rev}_a(p)\ge t}s^\star_{a,p}-\Pr[\mathrm{Rev}_a(r^{\mathcal R})\ge t]\le c\quad\text{for }t\le\beta^{(2)}_a.$$
--
--   Here $\beta^{(2)}_a$ is the second highest bid in auction $a$. Then Pro-LPR is a $(1+c)^{-1}$-approximation: for every reserve vector $r\ge0$,
--
--   $$\mathbb E\big[\mathrm{Rev}(r^{\rm out})\big]\ \ge\ \frac{1}{1+c}\,\mathrm{Rev}(r),$$
--
--   where $r^{\rm out}$ is the better of $r^{\mathcal R}$ and the zero vector, chosen per realization.
--
--   The lemma separates the analysis by auction. The approximation factor then follows from the two tail conditions (2) and (3) alone.
--
--   **Formalization Note.** "At least a $(1+c)^{-1}$ fraction of $\mathsf{ESP}^\star$" is stated as the bound against every nonnegative reserve vector. The expectation of $\mathrm{Rev}(r^{\rm out})$ is $\mathbb E[\max(\mathrm{Rev}(r^{\mathcal R}),\mathrm{Rev}(z))]$.
-- source:
--   Derakhshan, Golrezaei, Paes Leme, LP-based Approximation for Personalized Reserve Prices, arXiv:1905.01526v5, p. 9, Lemma 5.1, eqs. (2), (3)

import Mathlib
import Definitions.Def_ReserveLP_ProLPR_Model

namespace ReserveLP.ProLPR

theorem lemma_5_1 {A B : Type} [Fintype A] [Fintype B] [DecidableEq B] (D : DataSet A B)
    (s : A → Profile B → ℝ) (q : B → ℝ → ℝ) (hopt : LPOptimal D s q)
    (c : ℝ) (hc : 0 < c)
    (h2 : ∀ a : A, ∀ t : ℝ, 0 ≤ t → secondBid D a < t →
      profileMassGe D s a t - probRevGe D q a t ≤ 0)
    (h3 : ∀ a : A, ∀ t : ℝ, 0 ≤ t → t ≤ secondBid D a →
      profileMassGe D s a t - probRevGe D q a t ≤ c) :
    ∀ r : B → ℝ, (∀ b, 0 ≤ r b) → (1 + c)⁻¹ * rev D r ≤ expRevOut D q := by sorry

end ReserveLP.ProLPR
