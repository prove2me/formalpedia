-- Prove2me | Theorems.Thm_PolicyGradTheory_QNPG_estimation_term_bound
-- name    : PolicyGradTheory.QNPG.estimation_term_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T03:34:36.21704+00:00
-- url     : https://prove2.me/theorems/8459d21a-76f0-4dbb-8905-8d7612545b83
-- title:
--   (26), p. 39 — estimation term bounded by excess Q-risk
-- statement:
--   Let $w_\star$ minimize the Q-prediction loss at parameter θ over the Euclidean ball of radius W for the on-policy state-action measure $d^{\pi_\theta}_\nu$. Let w lie in the same ball, and suppose the covariance quadratic form of $d^\star$ is at most κ times that of ν. Then
--
--   $$
--   \mathbb E_{s\sim d^{\pi^\star}_\rho,a\sim\pi^\star}
--     [(w_\star-w)\cdot\nabla_\theta\log\pi_\theta(a\mid s)]
--     \le 2\sqrt{\frac{|A|\kappa}{1-\gamma}
--     \big(L(w;\theta,d^{\pi_\theta}_\nu)
--     -L(w_\star;\theta,d^{\pi_\theta}_\nu)\big)}.
--   $$
--
--   The statement relates excess fitting risk to the regret term without assuming a pointwise lower bound on the on-policy distribution.
--
--   **Formalization Note** The finite nonnegative relative condition number is represented by the covariance inequality for every direction, avoiding a zero denominator.
-- source:
--   arXiv:1908.00261v5, (26), proof of Theorem 6.1, pp. 39–40

import Mathlib
import Definitions.Def_PolicyGradTheory_QNPG_Setting

namespace PolicyGradTheory.QNPG

open FoundationsML.ReinforcementLearning

/-- Inequality (26), proof of Theorem 6.1, p. 39, with the exact constrained
least-squares minimizer and Assumption 6.2's covariance comparison. -/
theorem estimation_term_bound {S A : Type} [Fintype S] [DecidableEq S]
    [Fintype A] [DecidableEq A] [Nonempty A] {d : ℕ}
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ)
    (hM : PolicyGradTheory.ProjGA.IsFiniteMDP P r γ)
    (ρ : S → ℝ) (hρ : PolicyGradTheory.ProjGA.IsDist ρ)
    (ν : S × A → ℝ) (hν : PolicyGradTheory.ProjGA.IsDist ν)
    (πstar : S → A → ℝ) (hπstar : IsPolicy πstar)
    (φ : S → A → EuclideanSpace ℝ (Fin d))
    (κ : ℝ) (hκnonneg : 0 ≤ κ)
    (hκ : ∀ v, quadForm φ (dstar P γ ρ πstar) v ≤ κ * quadForm φ ν v)
    (W : ℝ) (θ wstar w : EuclideanSpace ℝ (Fin d))
    (hw : ‖w‖ ≤ W)
    (hmin : ‖wstar‖ ≤ W ∧
      ∀ v, ‖v‖ ≤ W →
        qLoss P r γ φ wstar θ (onPolicyMeasure (logLinearPolicy φ θ) P γ ν) ≤
          qLoss P r γ φ v θ (onPolicyMeasure (logLinearPolicy φ θ) P γ ν)) :
    (∑ s : S, PolicyGradTheory.ProjGA.visitation πstar P γ ρ s *
      ∑ a : A, πstar s a *
        inner ℝ (wstar - w)
          (gradient (fun x => Real.log (logLinearPolicy φ x s a)) θ)) ≤
      2 * Real.sqrt (((Fintype.card A : ℝ) * κ / (1 - γ)) *
        (qLoss P r γ φ w θ (onPolicyMeasure (logLinearPolicy φ θ) P γ ν) -
          qLoss P r γ φ wstar θ (onPolicyMeasure (logLinearPolicy φ θ) P γ ν))) := by sorry

end PolicyGradTheory.QNPG
