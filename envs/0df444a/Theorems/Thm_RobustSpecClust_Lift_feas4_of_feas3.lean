-- Prove2me | Theorems.Thm_RobustSpecClust_Lift_feas4_of_feas3
-- name    : RobustSpecClust.Lift.feas4_of_feas3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T09:43:29.389585+00:00
-- url     : https://prove2.me/theorems/8bd49d7e-5f81-43b3-8852-2f1d1b241aa9
-- title:
--   Appendix B (⇒): assignment lifting preserves feasibility and objective
-- statement:
--   If $Z$ is a feasible binary assignment matrix in formulation (3), then its Gram matrix $X=ZZ^\top$ is a feasible binary, positive semidefinite matrix of rank at most $r$ in formulation (4). For every real similarity matrix $K$ and penalty $\gamma$,
--
--   $$
--   F_4(ZZ^\top)=F_3(Z).
--   $$
--
--   This gives the forward direction of the correspondence between the two feasible programs.
-- source:
--   arXiv:1912.07546v3, Appendix B, proof of Proposition 1 (⇒), p. 37

import Mathlib
import Definitions.Def_RobustSpecClust_Lift_Setting

namespace RobustSpecClust.Lift

theorem feas4_of_feas3 {N r : ℕ} (K : Matrix (Fin N) (Fin N) ℝ) (γ : ℝ)
    (Z : Matrix (Fin N) (Fin r) ℝ) (hZ : Feas3 Z) :
    Feas4 r (Z * Z.transpose) ∧ obj4 K γ (Z * Z.transpose) = obj3 K γ Z := by sorry

end RobustSpecClust.Lift
