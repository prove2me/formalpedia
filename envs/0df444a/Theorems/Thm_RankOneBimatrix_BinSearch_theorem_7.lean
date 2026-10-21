-- Prove2me | Theorems.Thm_RankOneBimatrix_BinSearch_theorem_7
-- name    : RankOneBimatrix.BinSearch.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:34:11.074654+00:00
-- url     : https://prove2.me/theorems/542269b6-0d59-4abe-a48f-b04f91ff7504
-- title:
--   Theorem 7, p. 8 — projection of 𝒩 ∩ H
-- statement:
--   For $(A,C+ab^\top)$, form the auxiliary equilibrium set $\mathcal N$ in (8) and the hyperplane $H$ defined by $x^\top a=\lambda$. The Nash equilibrium set of the original game is exactly the projection of their intersection.
--
--   $$\operatorname{NE}(A,C+ab^\top)=\operatorname{proj}_{X\times Y}(\mathcal N\cap H).$$
--
--   This gives the geometric target for the search.
-- source:
--   Adsul, Garg, Mehta, Sohoni, von Stengel, Fast Algorithms for Rank-1 Bimatrix Games, arXiv:1812.04611v4, p. 8, Theorem 7 and (8)–(10)

import Definitions.Def_RankOneBimatrix_BinSearch_Setting

namespace RankOneBimatrix.BinSearch
open Matrix

/-- Theorem 7, p. 8: rank reduction by projecting `𝒩 ∩ H`. -/
theorem theorem_7 {m n : ℕ} (A C : Matrix (Fin m) (Fin n) ℝ)
    (a : Fin m → ℝ) (b : Fin n → ℝ) :
    {p : (Fin m → ℝ) × (Fin n → ℝ) |
      IsNE A (C + vecMulVec a b) p.1 p.2} =
    (fun q : ℝ × (Fin m → ℝ) × (Fin n → ℝ) => (q.2.1, q.2.2)) ''
      (NSetGeneral A C b ∩ Hyperplane a) := by sorry

end RankOneBimatrix.BinSearch
