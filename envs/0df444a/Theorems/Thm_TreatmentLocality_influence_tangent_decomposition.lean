-- Prove2me | Theorems.Thm_TreatmentLocality_influence_tangent_decomposition
-- name    : TreatmentLocality.influence_tangent_decomposition
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T03:39:05.648482+00:00
-- url     : https://prove2.me/theorems/10433ec4-1c20-42e5-976f-6537f4ecd948
-- title:
--   The influence function is a score direction of the SST family
-- statement:
--   **The influence function of the information-sharing estimator lies in the tangent space of the SST family.** Consider the SST experiment of arXiv:2407.19618 under the mixed policy $\pi^{1/2}$, with a stationary law $\nu$ in which every state is visited and rewards are integrable. Fix a direction $w$ and write
--   $$\varphi_w(X) \;=\; \sum_s w_s\, \nabla\hat\Delta_s\bigl(\mathbb{E}_\nu[u_{\mathrm{IS}}]\bigr)\bigl[u_{\mathrm{IS}}(X)\bigr]$$
--   for the linearisation of the model-based information-sharing estimator, evaluated on a single experiment step $X = (s, \gamma, s', r)$. Then there are functions $\alpha(s,a)$ and $\beta(s,a,j)$ such that, with $a = \mathrm{act}(\gamma, s)$ the executed action,
--   $$\varphi_w(X) \;=\; \alpha(s,a)\,\bigl(r - \bar r(s,a)\bigr) \;+\; \beta(s,a,s'),\qquad \sum_j P(j \mid s,a)\,\beta(s,a,j) = 0,$$
--   where $\bar r(s,a)$ is the mean reward at $(s,a)$.
--
--   This is the semiparametric content of the estimator's linearisation. The right-hand side is exactly the general form of a score of the SST family at $(s,a)$: the first term is the score of the reward law in the direction $\alpha(s,a)\,\sigma^2(s,a)$ of its mean, and the second is the score of the transition law in the direction $P(\cdot \mid s,a)\beta(s,a,\cdot)$, which is a legitimate perturbation of a probability vector precisely because it sums to zero. So $\varphi_w$ is a *score direction*, not merely a centred statistic — the step needed to pair it against an unbiased estimator through the information inequality.
--
--   Concretely, the decomposition is obtained by collapsing the influence function on a single observation into a difference of inverse-probability-weighted temporal-difference errors of the two arms' value functions, and reading off the coefficient of the reward and the coefficient of the realized next state. That the transition part is centred is the Bellman equation: at the crucial state the inverse-probability weight selects the arm whose action was executed, and away from it both arms execute the same action, so in either case the surviving temporal-difference residual is the one whose conditional mean the Bellman equation kills.
-- source:
--   H. Chen, D. Simchi-Levi, C. Wang, Improving the Estimation of Lifetime Effects in A/B Testing via Treatment Locality, arXiv:2407.19618v3, §6.2 (the information-sharing statistics), Appendix EC.3.2 (the linearisation of a differentiable estimator) and Appendix EC.4 (the parametrisation of the SST family and its scores). For the general framework see A. W. van der Vaart, Asymptotic Statistics, Cambridge 1998, Chapter 25 (tangent spaces and influence functions).

import Definitions.Def_TreatmentLocalityEstimator
import Mathlib.Probability.Kernel.Invariance

open MeasureTheory ProbabilityTheory TreatmentLocality
open scoped NNReal ENNReal

theorem TreatmentLocality.influence_tangent_decomposition {S : Type*} [DecidableEq S]
    [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (M : Model S) (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y))
    (hrint : Integrable (fun z : Step S => Step.rwd z) ν)
    (hμ : ∀ i, ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0) (w : S → ℝ) :
    ∃ (α : S → Bool → ℝ) (β : S → Bool → S → ℝ),
      (∀ (s : S) (γ : Bool),
        ∑ j, (M.trans s (M.act γ s) j).toReal * β s (M.act γ s) j = 0) ∧
      (∀ z : Step S,
        (∑ s, w s * fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν)
            (estObs M .IS z))
          = α (Step.state z) (M.act (Step.arm z) (Step.state z))
              * (Step.rwd z
                - ∫ x, x ∂(M.reward (Step.state z) (M.act (Step.arm z) (Step.state z))))
            + β (Step.state z) (M.act (Step.arm z) (Step.state z)) (Step.next z)) := by sorry
