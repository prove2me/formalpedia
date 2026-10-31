-- Prove2me | Theorems.Thm_ScalableMARL_lemma_13_norm_bounds
-- name    : ScalableMARL.lemma_13_norm_bounds
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:48:15.066222+00:00
-- url     : https://prove2.me/theorems/9ddbf701-f46e-45d0-bad7-23aae61ec446
-- title:
--   Lemma 13 — almost surely $\max(\|\hat g(m)\|,\|g(m)\|,\|h(m)\|,\|\nabla J(\theta(m))\|)\le\bar rL/(1-\gamma)^2$
-- statement:
--   Assume Assumption 1 ($0\le r_i\le\bar r$) and the gradient bound of Assumption 4 ($\|\nabla_{\theta_i}\log\zeta_i^{\theta_i}(a_i\mid s_i)\|\le L_i$, $L=\sqrt{\sum_iL_i^2}$), with policies that are distributions, positive and differentiable in their parameters, and critic step sizes $\alpha_t=h/(t+t_0)$ with $h>0$ and $t_0\ge2h$. Run SAC for $K$ outer iterations from any $\theta(0)$ with any actor step $\eta$. Then almost surely, for every outer iteration $m<K$,
--   $$\max\big(\|\hat g(m)\|,\|g(m)\|,\|h(m)\|,\|\nabla J(\theta(m))\|\big)\le\frac{\bar rL}{(1-\gamma)^2},$$
--   where $\hat g(m)$ is the actor's estimate (24), $g(m)$ the same with the true Q-functions (26), and $h(m)=h(\theta(m))$ its expectation (27).
--
--   These bounds are used throughout the proof of Theorem 4, in the descent inequality and in the martingale bound of Lemma 15.
--
--   **Formalization Note** "Almost surely" is: for every run with positive probability. Norms are the Euclidean norm of the whole parameter vector. Taking $K=M+1$ gives the page's range $m\le M$.
--
--   Differences from the source:
--   - generalization: the standing hypotheses of Theorem 4 → only Assumption 1, the gradient bound of Assumption 4, h > 0 and t₀ ≥ 2h; reason: these are implied by Theorem 4's hypotheses (h ≥ 2/σ > 0, t₀ ≥ 2h), and the page calls the lemma a consequence of Assumptions 1 and 4
--   - encoding: ∀ m ≤ M → every m < K for a run of K outer iterations; reason: K = M + 1 gives the page's range
--   - encoding: "almost surely" → for every run of positive probability; reason: the run has finitely many outcomes
--   - encoding: expectations and probabilities over the networked MDP → finite sums over the finite state-action spaces and over runs (Q_j^θ through the published one-step form r_j + γPV); reason: all spaces are finite, so these are the same numbers
--   - encoding: agents N = {1, …, n}, finite local sets S_i, A_i → Fin n and finite types; reason: Lean indexing
--   - reading: localized policies parameterized by θ_i (parameter space unnamed, norms Euclidean) → θ_i ∈ ℝ^{d_i}, θ in PiLp 2 with the Euclidean norm of the whole tuple; reason: the page differentiates in θ and uses Euclidean norms
--   - encoding: ∇_{θ_i} log ζ_i^{θ_i}(a_i|s_i) used as given → ζ_i^{θ_i}(a_i|s_i) > 0 and θ_i ↦ ζ_i^{θ_i}(a_i|s_i) differentiable; reason: presupposed for the gradient of the logarithm to exist; excludes only cases where the printed quantities are undefined
--   - encoding: the bounds S, A of Assumption 1 → real numbers Sb, Ab; reason: the page does not restrict them to integers; they do not enter this statement
-- source:
--   Qu, Wierman & Li, Scalable Reinforcement Learning for Multi-Agent Networked Systems, arXiv:1912.02906v3, p. 20, Lemma 13 (with eqs. (24), (26), (27))

import Mathlib
import Definitions.Def_ScalableMARL_NetworkedMDP
import Definitions.Def_ScalableMARL_Assumptions
import Definitions.Def_ScalableMARL_SAC

namespace ScalableMARL

variable {n : ℕ} {S A : Fin n → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
  [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]

/-- **Lemma 13 (almost-sure norm bounds).** Qu, Wierman & Li, arXiv:1912.02906v3, p. 20, Lemma 13:
almost surely, for all `m ≤ M`,
`max(‖ĝ(m)‖, ‖g(m)‖, ‖h(m)‖, ‖∇J(θ(m))‖) ≤ r̄L/(1 − γ)²`.

**Formalization Note.** "Almost surely" is: for every run `ω` of SAC over `K` outer iterations
with positive probability, and every `m < K` (`K = M + 1` gives the page's `m ≤ M`). `ĝ(m)` is
(24), `g(m)` is (26) on episode `m`, `h(m) = h(θ(m))` is (27), all at `θ(m)`; norms are Euclidean
on the whole parameter vector. Of the step-size conditions of Theorem 4 only `h > 0` and
`t₀ ≥ 2h` are assumed (they make `α_t ∈ (0, 1/2]`). -/
theorem lemma_13_norm_bounds (M : NetMDP n S A) (pol : LocalPolicyClass n S A)
    (hM : M.Valid) (hpol : pol.IsDistribution) (hpd : pol.PositiveDifferentiable)
    (rbar Sb Ab : ℝ) (L : Fin n → ℝ) (hA1 : Assumption1 M rbar Sb Ab)
    (hA4 : LogGradBound pol L) (κ T K : ℕ) (h t₀ η : ℝ) (hh : 0 < h) (ht₀ : 2 * h ≤ t₀)
    (θ₀ : pol.Param) (ω : Fin K → Episode S A T)
    (hω : 0 < runProb M pol κ h t₀ η θ₀ ω) (m : ℕ) (hm : m < K) :
    max (max ‖ghat M pol κ h t₀ (thetaRun M pol κ h t₀ η θ₀ ω m) (ω ⟨m, hm⟩)‖
          ‖gvec M pol κ (thetaRun M pol κ h t₀ η θ₀ ω m) (ω ⟨m, hm⟩)‖)
        (max ‖hvec M pol κ T (thetaRun M pol κ h t₀ η θ₀ ω m)‖
          ‖gradient (J M pol) (thetaRun M pol κ h t₀ η θ₀ ω m)‖) ≤
      rbar * Lnorm L / (1 - M.γ) ^ 2 := by sorry

end ScalableMARL
