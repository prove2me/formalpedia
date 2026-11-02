-- Prove2me | Theorems.Thm_RankOneBimatrix_BinSearch_br_extreme_exists
-- name    : RankOneBimatrix.BinSearch.br_extreme_exists
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-02T01:06:57.676982+00:00
-- url     : https://prove2.me/theorems/e11f8d8e-fd24-4528-9d01-f944b3275262
-- title:
--   Bounded $BR_{\max}$ / $BR_{\min}$ (29) have optimal extreme solutions
-- statement:
--   Let $m,n\ge1$, $A\in\mathbb R^{m\times n}$, $b\in\mathbb R^n$, $M\subseteq[m]$, $N\subseteq[n]$, and let $P(M,N)$ be the face (28) of the polyhedron $P$ in (27). If $P(M,N)$ is nonempty and $\lambda$ is bounded above on it, then
--
--   $$BR_{\max}(M,N):\ \max\ \lambda\ \text{ s.t. }(\lambda,x,v,s)\in P(M,N)$$
--
--   has an optimal solution that is an extreme point of $P(M,N)$; symmetrically, if $P(M,N)$ is nonempty and $\lambda$ is bounded below on it, then $BR_{\min}(M,N)$ has an optimal solution that is an extreme point of $P(M,N)$. (These are the LPs solved in lines 11 and 16 of Figure 2, which Theorem 19 assumes return extreme solutions.)
-- source:
--   Adsul, Garg, Mehta, Sohoni, von Stengel, Fast Algorithms for Rank-1 Bimatrix Games, arXiv:1812.04611v4, p. 13, LPs (29) with (27), (28); p. 20, Figure 2 lines 11 and 16; p. 21, Theorem 19; Bertsimas & Tsitsiklis, Introduction to Linear Optimization (1997), Theorem 2.8, p. 66

import Definitions.Def_RankOneBimatrix_BinSearch_Algorithm

namespace RankOneBimatrix.BinSearch
open Matrix

/-- If the face `P(M,N)` of (28) is nonempty and `λ` is bounded above (resp. below)
on it, then `BRmax(M,N)` (resp. `BRmin(M,N)`) of (29) has an optimal solution
that is an extreme point of `P(M,N)`. -/
theorem br_extreme_exists {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ)
    (M : Finset (Fin m)) (N : Finset (Fin n)) :
    ((PFace A b M N).Nonempty →
      BddAbove ((fun q : PolyPoint m n => q.1) '' PFace A b M N) →
      (BRmaxExtreme A b M N).Nonempty) ∧
    ((PFace A b M N).Nonempty →
      BddBelow ((fun q : PolyPoint m n => q.1) '' PFace A b M N) →
      (BRminExtreme A b M N).Nonempty) := by sorry

end RankOneBimatrix.BinSearch
