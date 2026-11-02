-- Prove2me | Theorems.Thm_RankOneBimatrix_BinSearch_primal_extreme_exists
-- name    : RankOneBimatrix.BinSearch.primal_extreme_exists
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-02T01:06:59.357722+00:00
-- url     : https://prove2.me/theorems/7e622ec2-ee44-4f92-9dce-93cc3d84b0c9
-- title:
--   LP $P_\lambda$ (19) has an optimal extreme solution
-- statement:
--   Let $m,n\ge 1$, $A\in\mathbb R^{m\times n}$, $b\in\mathbb R^n$ and $\lambda\in\mathbb R$. The parameterized LP
--
--   $$P_\lambda:\quad \min_{x,v,s}\ v\quad\text{s.t.}\quad A^\top x+\mathbf 1 v-s=b\lambda,\ \ \mathbf 1^\top x=1,\ \ x\ge 0,\ s\ge 0$$
--
--   has an optimal solution $(x,v,s)$ that is an extreme point of its feasible set.
--
--   This is the standing assumption of Theorem 19 that the LP solver used in line 6 of BINSEARCH (Figure 2) returns an extreme optimal solution: the feasible set is nonempty and contains no line, and $v$ is bounded below on it, so by the fundamental theorem of linear programming an optimum is attained at an extreme point.
-- source:
--   Adsul, Garg, Mehta, Sohoni, von Stengel, Fast Algorithms for Rank-1 Bimatrix Games, arXiv:1812.04611v4, p. 10, LP (19) (P_lambda), and p. 21, Theorem 19 (LPs solved by solvers returning extreme LP solutions); fundamental theorem of LP: Bertsimas & Tsitsiklis, Introduction to Linear Optimization (1997), Theorem 2.8, p. 66

import Definitions.Def_RankOneBimatrix_BinSearch_Algorithm

namespace RankOneBimatrix.BinSearch
open Matrix

/-- The LP `Pλ` of (19) has an optimal solution that is an extreme point of its feasible set. -/
theorem primal_extreme_exists {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ) (lam : ℝ) :
    (PExtreme A b lam).Nonempty := by sorry

end RankOneBimatrix.BinSearch
