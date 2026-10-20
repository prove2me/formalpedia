-- Prove2me | Theorems.Thm_ReserveLP_ProLPR_lemma_5_2
-- name    : ReserveLP.ProLPR.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:19:25.667977+00:00
-- url     : https://prove2.me/theorems/aea33aa7-6e3c-4f2d-9045-d0f4cc5eacc2
-- title:
--   Lemma 5.2, p. 10 — the first condition (8) holds: above β⁽²⁾ₐ the rounding loses no tail mass
-- statement:
--   Let $(s^\star,q^\star)$ be an optimal solution of Profile-LP, and let $r^{\mathcal R}$ be the random reserve vector of the Pro-LPR rounding. For every auction $a$ and every $t>\beta^{(2)}_a$,
--
--   $$\sum_{p\in\mathcal P_a,\ \mathrm{Rev}_a(p)\ge t}s^\star_{a,p}-\Pr\big[\mathrm{Rev}_a(r^{\mathcal R})\ge t\big]\ \le\ 0.$$
--
--   This is condition (2) of Lemma 5.1. Above the second highest bid, only the highest bidder's reserve can create revenue, and the rounding reproduces that event with at least the LP's weight.
-- source:
--   Derakhshan, Golrezaei, Paes Leme, LP-based Approximation for Personalized Reserve Prices, arXiv:1905.01526v5, p. 10, Lemma 5.2, eq. (8)

import Mathlib
import Definitions.Def_ReserveLP_ProLPR_Model

namespace ReserveLP.ProLPR

theorem lemma_5_2 {A B : Type} [Fintype A] [Fintype B] [DecidableEq B] (D : DataSet A B)
    (s : A → Profile B → ℝ) (q : B → ℝ → ℝ) (hopt : LPOptimal D s q) :
    ∀ a : A, ∀ t : ℝ, secondBid D a < t →
      profileMassGe D s a t - probRevGe D q a t ≤ 0 := by sorry

end ReserveLP.ProLPR
