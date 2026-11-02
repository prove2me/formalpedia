-- Prove2me | Theorems.Thm_RankOneBimatrix_BinSearch_dual_extreme_exists
-- name    : RankOneBimatrix.BinSearch.dual_extreme_exists
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-02T01:07:14.286617+00:00
-- url     : https://prove2.me/theorems/cb095746-0757-4d5c-b21d-58d241d61700
-- title:
--   LP $D_\lambda$ (17) has an optimal solution at a vertex of $D$
-- statement:
--   Let $m,n\ge 1$, $A\in\mathbb R^{m\times n}$, $b\in\mathbb R^n$ and $\lambda\in\mathbb R$. The LP
--
--   $$D_\lambda:\quad \max_{y,t}\ \lambda b^\top y+t\quad\text{s.t.}\quad (y,t)\in D=\{(y,t)\mid Ay+\mathbf 1t\le 0,\ \mathbf 1^\top y=1,\ y\ge 0\}$$
--
--   has an optimal solution that is an extreme point of $D$. This is the first sentence of the proof of Lemma 10: "The optimum of $D_\lambda$ exists for any $\lambda$ and is taken at a vertex of the polyhedron $D$ in (18)."
-- source:
--   Adsul, Garg, Mehta, Sohoni, von Stengel, Fast Algorithms for Rank-1 Bimatrix Games, arXiv:1812.04611v4, p. 11, proof of Lemma 10 (with (17), (18) on p. 10)

import Definitions.Def_RankOneBimatrix_BinSearch_Algorithm

namespace RankOneBimatrix.BinSearch
open Matrix

/-- The LP `Dλ` of (17) has an optimal solution that is an extreme point of `D`. -/
theorem dual_extreme_exists {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ) (lam : ℝ) :
    (DExtreme A b lam).Nonempty := by sorry

end RankOneBimatrix.BinSearch
