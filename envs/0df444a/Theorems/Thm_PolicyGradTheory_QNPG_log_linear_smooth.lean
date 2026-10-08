-- Prove2me | Theorems.Thm_PolicyGradTheory_QNPG_log_linear_smooth
-- name    : PolicyGradTheory.QNPG.log_linear_smooth
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T03:34:36.903323+00:00
-- url     : https://prove2.me/theorems/c59da376-32f1-4bd7-af9f-527e9f79dea0
-- title:
--   Remark 6.7, p. 33 — bounded log-linear features give B²-smooth log policies
-- statement:
--   For a log-linear policy with feature vectors of Euclidean norm at most B, the log probability of any fixed state-action pair has a B²-Lipschitz parameter gradient:
--
--   $$
--   \|\nabla_\theta\log\pi_\theta(a\mid s)-
--     \nabla_\theta\log\pi_{\theta'}(a\mid s)\|
--     \le B^2\|\theta-\theta'\|.
--   $$
--
--   This is the paper's smoothness condition for applying its deterministic NPG regret lemma to log-linear policies.
-- source:
--   arXiv:1908.00261v5, Remark 6.7, p. 33; smoothness definition (24), p. 37

import Mathlib
import Definitions.Def_PolicyGradTheory_QNPG_Setting

namespace PolicyGradTheory.QNPG

/-- Remark 6.7, p. 33, with smoothness understood as the gradient-Lipschitz
condition preceding (24), p. 37. -/
theorem log_linear_smooth {S A : Type} [Fintype A] [Nonempty A] {d : ℕ}
    (φ : S → A → EuclideanSpace ℝ (Fin d)) (B : ℝ)
    (hφ : ∀ s a, ‖φ s a‖ ≤ B) (s : S) (a : A) :
    ∀ θ θ' : EuclideanSpace ℝ (Fin d),
      ‖gradient (fun x => Real.log (logLinearPolicy φ x s a)) θ -
        gradient (fun x => Real.log (logLinearPolicy φ x s a)) θ'‖ ≤
        B ^ 2 * ‖θ - θ'‖ := by sorry

end PolicyGradTheory.QNPG
