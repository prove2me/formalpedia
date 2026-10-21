-- Prove2me | Theorems.Thm_ShorNonsmooth_NonlinEq_stage_endpoint_residual_quadratic
-- name    : ShorNonsmooth.NonlinEq.stage_endpoint_residual_quadratic
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T13:22:23.236997+00:00
-- url     : https://prove2.me/theorems/28403d26-26c4-45fd-b21c-49125a6a2a17
-- title:
--   The endpoint max residual of a short orthogonalization stage is quadratic
-- statement:
--   Under the hypotheses of Theorem 3.9, for fixed n there are ε > 0 and C > 0 such that every orthogonalization stage x₀, …, xₙ starting with ‖x₀‖ ≤ ε satisfies max_i |ψ_i(xₙ)| ≤ C‖x₀‖². This propagates the quadratic estimate (3.33) from each solved equation through all later order-orthogonal steps using Lemma 3.1.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, pp. 66–67, combining Eq. (3.33) with Lemma 3.1 through the fixed-length orthogonalization stage.

import Mathlib
import Definitions.Def_ShorNonsmooth_NonlinEq_maxResidual
import Definitions.Def_ShorNonsmooth_NonlinEq_orthStage

theorem ShorNonsmooth.NonlinEq.stage_endpoint_residual_quadratic {n : ℕ}
    (ψ : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (hψ : ∀ i, ContDiff ℝ 1 (ψ i)) (h0 : ∀ i, ψ i 0 = 0) (δ L : ℝ) (hδ : 0 < δ)
    (hLip : ∀ i, ∀ x' ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ,
      ∀ x'' ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ,
        ‖gradient (ψ i) x' - gradient (ψ i) x''‖ ≤ L * ‖x' - x''‖)
    (hind : LinearIndependent ℝ fun i => gradient (ψ i) (0 : EuclideanSpace ℝ (Fin n))) :
    ∃ ε > 0, ∃ C > 0, ∀ x : ℕ → EuclideanSpace ℝ (Fin n), IsOrthStage ψ x →
      ‖x 0‖ ≤ ε → maxResidual ψ (x n) ≤ C * ‖x 0‖ ^ 2 := by sorry
