-- Prove2me | Theorems.Thm_PolicyGradTheory_QNPG_qnpg_agnostic_bound
-- name    : PolicyGradTheory.QNPG.qnpg_agnostic_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T03:34:51.418155+00:00
-- url     : https://prove2.me/theorems/8c1ff012-0dab-4a9d-bbd8-c15818e5946d
-- title:
--   Theorem 6.1, p. 29 — agnostic Q-NPG bound from transfer error, excess risk and conditioning
-- statement:
--   Fix finite state and action sets, a discounted MDP with rewards in [0,1], a start distribution ρ, a state-action fitting distribution ν, and any comparator policy π⋆. Let πθ be the log-linear class with feature norms at most B. Q-NPG starts from $\theta^{(0)}=0$ and updates with random directions $w^{(t)}$ in the radius-W ball and step size $\eta=\sqrt{2\log|A|/(B^2W^2T)}$. At each $t<T$, let $w_\star^{(t)}$ be an exact radius-W minimizer of the Q-prediction loss under the on-policy measure $d^{(t)}$.
--
--   Suppose the relative covariance bound with constant κ holds between $d^\star=d^{\pi^\star}_\rho\times\mathrm{Unif}_A$ and ν. Suppose the expected excess risk is at most εstat and the expected transfer loss $L(w_\star^{(t)};\theta^{(t)},d^\star)$ is at most εbias at every $t<T$. Then
--
--   $$
--   \mathbb E\!\left[\min_{t<T}\{V^{\pi^\star}(\rho)-V^{\pi_{\theta^{(t)}}}(\rho)\}\right]
--   \le \frac{BW}{1-\gamma}\sqrt{\frac{2\log|A|}{T}}
--   +\sqrt{\frac{4|A|\kappa\varepsilon_{\rm stat}}{(1-\gamma)^3}}
--   +\frac{\sqrt{4|A|\varepsilon_{\rm bias}}}{1-\gamma}.
--   $$
--
--   The result guarantees competition with an arbitrary comparison policy; optimality of π⋆ is not assumed.
--
--   **Formalization Note** The finite setting and reward range come from §3. Nonempty A and positive B, W and T make the uniform policy, step size and minimum well-defined. Random directions and exact minimizers are measurable, which makes these bounded-loss expectations integrable. κ is a nonnegative quadratic-form upper bound, which includes the finite coefficient of Assumption 6.2. The minimum is taken separately for each random run before expectation.
-- source:
--   arXiv:1908.00261v5, Theorem 6.1, p. 29; Assumptions 6.1–6.2, pp. 28–29

import Mathlib
import Definitions.Def_PolicyGradTheory_QNPG_Setting

namespace PolicyGradTheory.QNPG

open FoundationsML.ReinforcementLearning MeasureTheory

/-- Theorem 6.1, p. 29: agnostic Q-NPG for a log-linear policy class. -/
theorem qnpg_agnostic_bound {S A : Type} [Fintype S] [DecidableEq S]
    [Fintype A] [DecidableEq A] [Nonempty A] (d : ℕ)
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ)
    (hM : PolicyGradTheory.ProjGA.IsFiniteMDP P r γ)
    (ρ : S → ℝ) (hρ : PolicyGradTheory.ProjGA.IsDist ρ)
    (ν : S × A → ℝ) (hν : PolicyGradTheory.ProjGA.IsDist ν)
    (πstar : S → A → ℝ) (hπstar : IsPolicy πstar)
    (φ : S → A → EuclideanSpace ℝ (Fin d))
    (B : ℝ) (hB : 0 < B) (hφ : ∀ s a, ‖φ s a‖ ≤ B)
    (W : ℝ) (hW : 0 < W)
    (κ : ℝ) (hκnonneg : 0 ≤ κ)
    (hκ : ∀ v, quadForm φ (dstar P γ ρ πstar) v ≤ κ * quadForm φ ν v)
    (T : ℕ) (hT : 0 < T)
    (η : ℝ) (hη : η = Real.sqrt (2 * Real.log (Fintype.card A : ℝ) /
      (B ^ 2 * W ^ 2 * T)))
    {Ω : Type*} [MeasurableSpace Ω] (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
    (w wstar : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hwm : ∀ t < T, Measurable (w t))
    (hwstarm : ∀ t < T, Measurable (wstar t))
    (hwW : ∀ t < T, ∀ ω, ‖w t ω‖ ≤ W)
    (hwstar : ∀ t < T, ∀ ω,
      ‖wstar t ω‖ ≤ W ∧
        ∀ v, ‖v‖ ≤ W →
          qLoss P r γ φ (wstar t ω) (qnpgParams η w t ω)
            (onPolicyMeasure (logLinearPolicy φ (qnpgParams η w t ω)) P γ ν) ≤
          qLoss P r γ φ v (qnpgParams η w t ω)
            (onPolicyMeasure (logLinearPolicy φ (qnpgParams η w t ω)) P γ ν))
    (εstat εbias : ℝ)
    (hstat : ∀ t < T,
      (∫ ω, (qLoss P r γ φ (w t ω) (qnpgParams η w t ω)
                (onPolicyMeasure (logLinearPolicy φ (qnpgParams η w t ω)) P γ ν) -
              qLoss P r γ φ (wstar t ω) (qnpgParams η w t ω)
                (onPolicyMeasure (logLinearPolicy φ (qnpgParams η w t ω)) P γ ν)) ∂ℙ) ≤ εstat)
    (hbias : ∀ t < T,
      (∫ ω, qLoss P r γ φ (wstar t ω) (qnpgParams η w t ω)
        (dstar P γ ρ πstar) ∂ℙ) ≤ εbias) :
    (∫ ω, (Finset.range T).inf' (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hT))
      (fun t => PolicyGradTheory.ProjGA.valueAt πstar P r γ ρ -
        PolicyGradTheory.ProjGA.valueAt (logLinearPolicy φ (qnpgParams η w t ω)) P r γ ρ) ∂ℙ) ≤
      B * W / (1 - γ) * Real.sqrt (2 * Real.log (Fintype.card A : ℝ) / T) +
      Real.sqrt (4 * (Fintype.card A : ℝ) * κ * εstat / (1 - γ) ^ 3) +
      Real.sqrt (4 * (Fintype.card A : ℝ) * εbias) / (1 - γ) := by sorry

end PolicyGradTheory.QNPG
