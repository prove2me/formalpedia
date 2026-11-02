-- Prove2me | Theorems.Thm_RankOneBimatrix_BinSearch_strong_duality
-- name    : RankOneBimatrix.BinSearch.strong_duality
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-02T01:07:07.720237+00:00
-- url     : https://prove2.me/theorems/1dbce2ec-be2c-4038-80a2-3d809747b2f3
-- title:
--   LP duality for $P_\lambda$ and $D_\lambda$
-- statement:
--   Let $m,n\ge 1$, $A\in\mathbb R^{m\times n}$, $b\in\mathbb R^n$ and $\lambda\in\mathbb R$. The LP $P_\lambda$ in (19) is the LP dual of $D_\lambda$ in (17). Both have optimal solutions, and the optimal values coincide: there are an optimal $(x,v,s)$ of $P_\lambda$ and an optimal $(y,t)$ of $D_\lambda$ with
--
--   $$v=\lambda b^\top y+t.$$
--
--   This is the statement "For optimal solutions $(y,t)$ to $D_\lambda$ and $(x,v,s)$ to $P_\lambda$ we have $\lambda b^\top y+t=v$" on p. 10 (LP duality).
-- source:
--   Adsul, Garg, Mehta, Sohoni, von Stengel, Fast Algorithms for Rank-1 Bimatrix Games, arXiv:1812.04611v4, p. 10, sentence after (19): 'The LP D_lambda is the dual of ... P_lambda' and 'For optimal solutions (y,t) to D_lambda and (x,v,s) to P_lambda we have lambda b^T y + t = v'

import Definitions.Def_RankOneBimatrix_BinSearch_Algorithm

namespace RankOneBimatrix.BinSearch
open Matrix

/-- LP duality for the dual pair `Pλ` (19) and `Dλ` (17): both have optimal
solutions, with equal optimal values. -/
theorem strong_duality {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ) (lam : ℝ) :
    ∃ p ∈ POpt A b lam, ∃ q ∈ Yopt A b lam, p.2.1 = DValue b lam q := by sorry

end RankOneBimatrix.BinSearch
