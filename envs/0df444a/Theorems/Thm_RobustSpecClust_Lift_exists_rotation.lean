-- Prove2me | Theorems.Thm_RobustSpecClust_Lift_exists_rotation
-- name    : RobustSpecClust.Lift.exists_rotation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T09:43:25.679516+00:00
-- url     : https://prove2.me/theorems/656c4db1-7d3e-42ed-b27c-58a083d72203
-- title:
--   Appendix B (⇐): an orthogonal rotation yields an assignment matrix
-- statement:
--   Let $G$ be a real $N\times r$ matrix whose Gram matrix $GG^\top$ has only zero-one entries. There exists an $r\times r$ orthogonal matrix $O$ for which $Z=GO$ is a feasible assignment matrix in (3): every entry of $Z$ is zero or one, and every row sums to at most one.
--
--   $$
--   O^\top O=I_r,\qquad Z=GO\in\{0,1\}^{N\times r},\qquad Z\mathbf 1_r\le\mathbf 1_N.
--   $$
--
--   The distinct nonzero rows of $G$ are orthogonal, so their number is at most $r$; the remaining coordinate directions accommodate zero rows and unused clusters.
-- source:
--   arXiv:1912.07546v3, Appendix B, proof of Proposition 1 (⇐), p. 38, final claim

import Mathlib
import Definitions.Def_RobustSpecClust_Lift_Setting

namespace RobustSpecClust.Lift

theorem exists_rotation {N r : ℕ} (G : Matrix (Fin N) (Fin r) ℝ)
    (hbinary : ∀ i j, (G * G.transpose) i j = 0 ∨ (G * G.transpose) i j = 1) :
    ∃ O ∈ Matrix.orthogonalGroup (Fin r) ℝ, Feas3 (G * O) := by sorry

end RobustSpecClust.Lift
