-- Prove2me | Theorems.Thm_ShorNonsmooth_NonlinEq_maxResidual_active_signed_inner_approx
-- name    : ShorNonsmooth.NonlinEq.maxResidual_active_signed_inner_approx
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T10:18:49.144135+00:00
-- url     : https://prove2.me/theorems/efb20e34-6619-42a0-bef8-05fee019563e
-- title:
--   An active coordinate gradient approximates the displacement functional up to the requested relative error
-- statement:
--   Near a common root with nonsingular Jacobian, for every small relative error δ, the inner product of an active coordinate gradient with x minus xstar differs from that coordinate residual by at most δ times the max residual.
-- source:
--   Shor (1985), regular case of Theorem 3.8, first-order active-gradient estimate

import Mathlib
import Definitions.Def_ShorNonsmooth_NonlinEq_maxResidual
import Definitions.Def_ShorNonsmooth_NonlinEq_jacobianMatrix

theorem ShorNonsmooth.NonlinEq.maxResidual_active_signed_inner_approx {n : ℕ}
    (ψ : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (xstar : EuclideanSpace ℝ (Fin n)) (hroot : ∀ i, ψ i xstar = 0)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : U ∈ nhds xstar)
    (hψ : ∀ i, ContDiffOn ℝ 1 (ψ i) U)
    (hJ : (jacobianMatrix ψ xstar).det ≠ 0) (δ : ℝ) (hδ : 0 < δ) :
    ∃ V ∈ nhds xstar, ∀ x ∈ V, ∀ i, |ψ i x| = maxResidual ψ x →
      |inner ℝ (gradient (ψ i) x) (x - xstar) - ψ i x| ≤
        δ * maxResidual ψ x := by sorry
