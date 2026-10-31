-- Prove2me | Theorems.Thm_ScalableMARL_lemma_15_martingale_term
-- name    : ScalableMARL.lemma_15_martingale_term
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:48:22.877+00:00
-- url     : https://prove2.me/theorems/4136743d-010c-4fda-8699-8c42e55fc222
-- title:
--   Lemma 15 — with probability $\ge1-\delta/2$, $|\sum_{m<M}\eta_m\langle\nabla J(\theta(m)),e^2(m)\rangle|\le\frac{2\bar r^2L^2}{(1-\gamma)^4}\sqrt{2\sum_m\eta_m^2\log\frac4\delta}$
-- statement:
--   Assume Assumption 1 ($0\le r_i\le\bar r$) and the gradient bound of Assumption 4 ($\|\nabla_{\theta_i}\log\zeta_i^{\theta_i}(a_i\mid s_i)\|\le L_i$, $L=\sqrt{\sum_iL_i^2}$), with policies that are distributions, positive and differentiable in their parameters. Run SAC for $M$ outer iterations from any $\theta(0)$, with actor steps $\eta_m=\eta/\sqrt{m+1}$, $\eta>0$, and let $\delta\in(0,1)$. Then with probability at least $1-\delta/2$,
--   $$\Big|\sum_{m=0}^{M-1}\eta_m\big\langle\nabla J(\theta(m)),e^2(m)\big\rangle\Big|\le\frac{2\bar r^2L^2}{(1-\gamma)^4}\sqrt{2\sum_{m=0}^{M-1}\eta_m^2\log\frac4\delta},$$
--   where $e^2(m)=g(m)-h(m)$ is the difference between the sampled gradient (26) and its expectation (27).
--
--   Since $\theta(m)$ is determined by the first $m$ episodes and episode $m$ is drawn under $\theta(m)$, the terms $\eta_m\langle\nabla J(\theta(m)),e^2(m)\rangle$ form a bounded martingale difference sequence; the lemma is the resulting Azuma–Hoeffding bound.
--
--   **Formalization Note** The probability is under the law of the SAC run (each episode drawn under the current $\theta(m)$), for any critic parameters $h$, $t_0$ and hop count $\kappa$.
--
--   Differences from the source:
--   - generalization: the standing hypotheses of Theorem 4 → only Assumption 1, the gradient bound of Assumption 4, η > 0 and δ ∈ (0, 1); reason: the statement holds without the other hypotheses, which are part of Theorem 4's
--   - encoding: expectations and probabilities over the networked MDP → finite sums over the finite state-action spaces and over runs (Q_j^θ through the published one-step form r_j + γPV); reason: all spaces are finite, so these are the same numbers
--   - encoding: agents N = {1, …, n}, finite local sets S_i, A_i → Fin n and finite types; reason: Lean indexing
--   - reading: localized policies parameterized by θ_i (parameter space unnamed, norms Euclidean) → θ_i ∈ ℝ^{d_i}, θ in PiLp 2 with the Euclidean norm of the whole tuple; reason: the page differentiates in θ and uses Euclidean norms
--   - encoding: ∇_{θ_i} log ζ_i^{θ_i}(a_i|s_i) used as given → ζ_i^{θ_i}(a_i|s_i) > 0 and θ_i ↦ ζ_i^{θ_i}(a_i|s_i) differentiable; reason: presupposed for the gradient of the logarithm to exist; excludes only cases where the printed quantities are undefined
--   - encoding: the bounds S, A of Assumption 1 → real numbers Sb, Ab; reason: the page does not restrict them to integers; they do not enter this statement
-- source:
--   Qu, Wierman & Li, Scalable Reinforcement Learning for Multi-Agent Networked Systems, arXiv:1912.02906v3, p. 20, Lemma 15 (with eqs. (26)–(28))

import Mathlib
import Definitions.Def_ScalableMARL_NetworkedMDP
import Definitions.Def_ScalableMARL_Assumptions
import Definitions.Def_ScalableMARL_SAC

namespace ScalableMARL

variable {n : ℕ} {S A : Fin n → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
  [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]

/-- **Lemma 15 (the martingale term `e²`).** Qu, Wierman & Li, arXiv:1912.02906v3, p. 20, Lemma 15:
with probability at least `1 − δ/2`,
`|Σ_{m=0}^{M−1} η_m ⟨∇J(θ(m)), e²(m)⟩| ≤ (2r̄²L²/(1 − γ)⁴) √(2 Σ_{m=0}^{M−1} η_m² log(4/δ))`,
where `e²(m) = g(m) − h(m)` (28) and `η_m = η/√(m + 1)`.

**Formalization Note.** Assumptions 1 and the bound `‖∇_{θ_i} log ζ_i‖ ≤ L_i` of Assumption 4 are
assumed, with `η > 0` and `δ ∈ (0, 1)`. The probability is under the law of the SAC run over `M`
outer iterations from an arbitrary `θ(0)`, with any critic step sizes `h, t₀` and hop count `κ`. -/
theorem lemma_15_martingale_term (M : NetMDP n S A) (pol : LocalPolicyClass n S A)
    (hM : M.Valid) (hpol : pol.IsDistribution) (hpd : pol.PositiveDifferentiable)
    (rbar Sb Ab h t₀ η δ : ℝ) (L : Fin n → ℝ) (κ T Mo : ℕ)
    (hA1 : Assumption1 M rbar Sb Ab) (hA4 : LogGradBound pol L)
    (hη : 0 < η) (hδ0 : 0 < δ) (hδ1 : δ < 1) (θ₀ : pol.Param) :
    1 - δ / 2 ≤ runProbOf M pol κ h t₀ η θ₀ {ω : Fin Mo → Episode S A T |
      |∑ m : Fin Mo, actorStep η m *
          inner ℝ (gradient (J M pol) (thetaRun M pol κ h t₀ η θ₀ ω m))
            (gvec M pol κ (thetaRun M pol κ h t₀ η θ₀ ω m) (ω m) -
              hvec M pol κ T (thetaRun M pol κ h t₀ η θ₀ ω m))| ≤
        2 * rbar ^ 2 * Lnorm L ^ 2 / (1 - M.γ) ^ 4 *
          Real.sqrt (2 * (∑ m : Fin Mo, actorStep η m ^ 2) * Real.log (4 / δ))} := by sorry

end ScalableMARL
