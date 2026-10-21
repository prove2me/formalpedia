-- Prove2me | Theorems.Thm_ShorNonsmooth_NonlinEq_stage_component_residual_quadratic
-- name    : ShorNonsmooth.NonlinEq.stage_component_residual_quadratic
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T14:34:21.168593+00:00
-- url     : https://prove2.me/theorems/4cebd027-58ee-45f9-b27c-450becd3a68f
-- title:
--   Each component residual at the endpoint of a stage is quadratic
-- statement:
--   Fix one coordinate k. Under the hypotheses of Theorem 3.9, there are positive constants ε and C such that every orthogonalization stage starting with ‖x₀‖ ≤ ε satisfies |ψ_k(xₙ)| ≤ C‖x₀‖². The residual created by step k is quadratic by Eq. (3.33), and every later order-orthogonal step changes it only by another quadratic amount by Lemma 3.1.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, pp. 66–67, Eq. (3.33) together with Lemma 3.1, applied to one component through the remaining ordered steps.

import Mathlib
import Definitions.Def_ShorNonsmooth_NonlinEq_orthStage

theorem ShorNonsmooth.NonlinEq.stage_component_residual_quadratic {n : ℕ}
    (ψ : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (hψ : ∀ i, ContDiff ℝ 1 (ψ i)) (h0 : ∀ i, ψ i 0 = 0) (δ L : ℝ) (hδ : 0 < δ)
    (hLip : ∀ i, ∀ x' ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ,
      ∀ x'' ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ,
        ‖gradient (ψ i) x' - gradient (ψ i) x''‖ ≤ L * ‖x' - x''‖)
    (hind : LinearIndependent ℝ fun i => gradient (ψ i) (0 : EuclideanSpace ℝ (Fin n)))
    (k : Fin n) :
    ∃ ε > 0, ∃ C > 0, ∀ x : ℕ → EuclideanSpace ℝ (Fin n), IsOrthStage ψ x →
      ‖x 0‖ ≤ ε → |ψ k (x n)| ≤ C * ‖x 0‖ ^ 2 := by sorry
