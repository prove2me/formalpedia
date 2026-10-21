-- Prove2me | Theorems.Thm_ShorNonsmooth_NonlinEq_stage_orthDir_prefix_inline
-- name    : ShorNonsmooth.NonlinEq.stage_orthDir_prefix_inline
-- status  : Open
-- author  : @WillR
-- created : 2026-10-20T14:15:50.813121+00:00
-- url     : https://prove2.me/theorems/7ccd8d35-826e-48ff-bc85-d0b0741e9cd7
-- title:
--   A prefix-uniform lower bound for ordered orthogonal directions
-- statement:
--   Under the hypotheses of Theorem 3.9, there are a radius η and a positive constant b such that, for every ordered step k whose preceding points x₀,…,xₖ lie within radius η, the orthogonalized gradient at step k has norm at least b.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, pp. 65–66, Eq. (3.29), in the prefix form required by the fixed-length stage induction.

import Mathlib
import Definitions.Def_ShorNonsmooth_NonlinEq_orthStage

theorem ShorNonsmooth.NonlinEq.stage_orthDir_prefix_inline {n : ℕ}
    (ψ : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (hψ : ∀ i, ContDiff ℝ 1 (ψ i))
    (hind : LinearIndependent ℝ fun i => gradient (ψ i) (0 : EuclideanSpace ℝ (Fin n))) :
    ∃ η > 0, ∃ b > 0, ∀ x : ℕ → EuclideanSpace ℝ (Fin n), ∀ k : Fin n,
      (∀ j : Fin (k.val + 1), ‖x j.val‖ < η) → b ≤ ‖orthDir ψ x k‖ := by sorry
