-- Prove2me | Theorems.Thm_RankOneBimatrix_BinSearch_pmax_pmin_extreme_exists
-- name    : RankOneBimatrix.BinSearch.pmax_pmin_extreme_exists
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-02T01:07:16.647531+00:00
-- url     : https://prove2.me/theorems/9bcdd1e5-7972-4e28-bdf6-df11c2b51aa9
-- title:
--   Feasible $P_{\max}$ / $P_{\min}$ (39) have optimal extreme solutions
-- statement:
--   Let $m,n\ge1$, $A\in\mathbb R^{m\times n}$, $a\in\mathbb R^m$, $b\in\mathbb R^n$, $M\subseteq[m]$, $N\subseteq[n]$ and $\lambda'\in\mathbb R$. Consider the LPs of (39),
--
--   $$P_{\max}(M,N,a,\lambda'):\ \max\ \lambda-x^\top a\ \text{ s.t. }(\lambda,x,v,s)\in P(M,N),\ x^\top a\ge\lambda\ge\lambda',$$
--
--   $$P_{\min}(M,N,a,\lambda'):\ \min\ \lambda-x^\top a\ \text{ s.t. }(\lambda,x,v,s)\in P(M,N),\ x^\top a\le\lambda\le\lambda',$$
--
--   where $P(M,N)$ is the face (28) of the polyhedron $P$ in (27). If $P_{\max}(M,N,a,\lambda')$ is feasible, it has an optimal solution that is an extreme point of its feasible set; likewise for $P_{\min}(M,N,a,\lambda')$. (The objective is bounded by $0$ and the feasible sets contain no line, so this is the fundamental theorem of LP; Theorem 19 assumes these LPs, solved in lines 9 and 14 of Figure 2, return extreme solutions.)
-- source:
--   Adsul, Garg, Mehta, Sohoni, von Stengel, Fast Algorithms for Rank-1 Bimatrix Games, arXiv:1812.04611v4, p. 18, LPs (39); p. 21, Theorem 19 (solvers return extreme LP solutions); Bertsimas & Tsitsiklis, Introduction to Linear Optimization (1997), Theorem 2.8, p. 66

import Definitions.Def_RankOneBimatrix_BinSearch_Algorithm

namespace RankOneBimatrix.BinSearch
open Matrix

/-- If the LP `Pmax(M,N,a,λ')` (resp. `Pmin(M,N,a,λ')`) of (39) is feasible, then it
has an optimal solution that is an extreme point of its feasible set. -/
theorem pmax_pmin_extreme_exists {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (A : Matrix (Fin m) (Fin n) ℝ) (a : Fin m → ℝ) (b : Fin n → ℝ)
    (M : Finset (Fin m)) (N : Finset (Fin n)) (lam' : ℝ) :
    ((PmaxFeas A a b M N lam').Nonempty →
      (PmaxExtreme A a b M N lam').Nonempty) ∧
    ((PminFeas A a b M N lam').Nonempty →
      (PminExtreme A a b M N lam').Nonempty) := by sorry

end RankOneBimatrix.BinSearch
