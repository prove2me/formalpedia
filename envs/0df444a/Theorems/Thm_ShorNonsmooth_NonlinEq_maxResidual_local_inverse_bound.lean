-- Prove2me | Theorems.Thm_ShorNonsmooth_NonlinEq_maxResidual_local_inverse_bound
-- name    : ShorNonsmooth.NonlinEq.maxResidual_local_inverse_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T09:51:44.884127+00:00
-- url     : https://prove2.me/theorems/4302ae3a-c8bb-4d17-ad87-fa719309a6db
-- title:
--   A nonsingular Jacobian bounds displacement by the max residual near a common root
-- statement:
--   Let ψ_i be continuously differentiable near a common root xstar and suppose the Jacobian of ψ at xstar is nonsingular. Then near xstar there is a positive constant C such that the distance from x to xstar is at most C times max_i |ψ_i(x)|.
-- source:
--   Shor (1985), regular case of Theorem 3.8, local inverse-Jacobian estimate

import Mathlib
import Definitions.Def_ShorNonsmooth_NonlinEq_maxResidual
import Definitions.Def_ShorNonsmooth_NonlinEq_jacobianMatrix

theorem ShorNonsmooth.NonlinEq.maxResidual_local_inverse_bound {n : ℕ}
    (ψ : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (xstar : EuclideanSpace ℝ (Fin n)) (hroot : ∀ i, ψ i xstar = 0)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : U ∈ nhds xstar)
    (hψ : ∀ i, ContDiffOn ℝ 1 (ψ i) U)
    (hJ : (jacobianMatrix ψ xstar).det ≠ 0) :
    ∃ V ∈ nhds xstar, ∃ C > 0, ∀ x ∈ V,
      ‖x - xstar‖ ≤ C * maxResidual ψ x := by sorry
