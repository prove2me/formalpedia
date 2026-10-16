-- Prove2me | Theorems.Thm_RobustSpecClust_Lift_exists_factor
-- name    : RobustSpecClust.Lift.exists_factor
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T09:43:37.730551+00:00
-- url     : https://prove2.me/theorems/e14d0f9a-4138-4a3e-a75a-8a107308f56b
-- title:
--   Appendix B (⇐): rank-bounded PSD factorization
-- statement:
--   Let $X$ be a real $N\times N$ positive semidefinite matrix with $\operatorname{rank}(X)\le r$. There is a real $N\times r$ matrix $G$ such that
--
--   $$
--   X=GG^\top,\qquad \operatorname{rank}(G)=\operatorname{rank}(X).
--   $$
--
--   This places the factor of a lifted feasible matrix in the same $r$-dimensional cluster-coordinate space as an assignment matrix.
-- source:
--   arXiv:1912.07546v3, Appendix B, proof of Proposition 1 (⇐), p. 37, first claim

import Mathlib
import Definitions.Def_RobustSpecClust_Lift_Setting

namespace RobustSpecClust.Lift

theorem exists_factor {N r : ℕ} (X : Matrix (Fin N) (Fin N) ℝ)
    (hpsd : X.PosSemidef) (hrank : X.rank ≤ r) :
    ∃ G : Matrix (Fin N) (Fin r) ℝ, X = G * G.transpose ∧ G.rank = X.rank := by sorry

end RobustSpecClust.Lift
