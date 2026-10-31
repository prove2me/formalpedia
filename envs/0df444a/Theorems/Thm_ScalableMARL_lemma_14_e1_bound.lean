-- Prove2me | Theorems.Thm_ScalableMARL_lemma_14_e1_bound
-- name    : ScalableMARL.lemma_14_e1_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:48:25.63543+00:00
-- url     : https://prove2.me/theorems/4cac27cb-b6bf-44ad-bd96-9b64f9f0994c
-- title:
--   Lemma 14 — under (12), with probability $\ge1-\delta/2$, $\sup_{m<M}\|\hat g(m)-g(m)\|\le4cL\rho^{\kappa+1}/(1-\gamma)^3$
-- statement:
--   Assume Assumptions 1, 2 and 3, the gradient bound $\|\nabla_{\theta_i}\log\zeta_i^{\theta_i}(a_i\mid s_i)\|\le L_i$ of Assumption 4 ($L=\sqrt{\sum_iL_i^2}$), the critic step-size conditions $h\ge\frac1\sigma\max(2,\frac1{1-\sqrt\gamma})$, $t_0\ge\max(2h,4\sigma h,\tau)$, and $\delta\in(0,1)$. Suppose $T$ is large enough that
--   $$\frac{C_a(\frac{\delta}{2nM},T)}{\sqrt{T+t_0}}+\frac{C_a'}{T+t_0}\le\frac{2c\rho^{\kappa+1}}{(1-\gamma)^2},$$
--   with $C_a$, $C_a'$, $\bar\epsilon$ as in Theorem 4. Run SAC for $M$ outer iterations from any $\theta(0)$. Then with probability at least $1-\delta/2$,
--   $$\sup_{0\le m\le M-1}\|e^1(m)\|\le\frac{4cL\rho^{\kappa+1}}{(1-\gamma)^3},\qquad e^1(m)=\hat g(m)-g(m).$$
--
--   The term $e^1$ is the error of the actor's gradient estimate caused by using the critic's tables instead of the true Q-functions; the lemma combines Theorem 5 for every agent and every outer iteration with a union bound.
--
--   **Formalization Note** The probability is under the law of the SAC run (each episode drawn under the current $\theta(m)$). The network has $n\ge1$ agents.
--
--   Differences from the source:
--   - generalization: the standing hypotheses of Theorem 4 → Assumptions 1–3, the gradient bound of Assumption 4, the conditions on h, t₀ and δ; the Lipschitz part of Assumption 4, M ≥ 3 and the conditions on η are not assumed; reason: the statement holds without them and they are part of Theorem 4's hypotheses
--   - encoding: a network of agents N = {1, …, n} → n ≥ 1; reason: the page divides by n in δ/(2nM); excludes only the case where (12) is undefined
--   - encoding: sup_{0≤m≤M−1} → for every m < M; reason: same statement
--   - encoding: expectations and probabilities over the networked MDP → finite sums over the finite state-action spaces and over runs (Q_j^θ through the published one-step form r_j + γPV); reason: all spaces are finite, so these are the same numbers
--   - encoding: agents N = {1, …, n}, finite local sets S_i, A_i → Fin n and finite types; reason: Lean indexing
--   - reading: localized policies parameterized by θ_i (parameter space unnamed, norms Euclidean) → θ_i ∈ ℝ^{d_i}, θ in PiLp 2 with the Euclidean norm of the whole tuple; reason: the page differentiates in θ and uses Euclidean norms
--   - reading: Assumption 3's P(z_{N_i^κ}(τ) = x | z(1) = z) ≥ σ → the (τ−1)-step law of the state-action chain from z puts mass ≥ σ on {z' : z'_{N_i^κ} = x}; reason: the chain is time homogeneous and z(1) to z(τ) is τ − 1 transitions
--   - reading: Definition 1 with κ unspecified, in Assumption 2 → the exponential decay property at the algorithm's κ; reason: κ is the algorithm's fixed parameter throughout; the proof uses only that κ
--   - encoding: the bounds S, A of Assumption 1 → real numbers Sb, Ab; reason: the page does not restrict them to integers; they enter only through log SA
-- source:
--   Qu, Wierman & Li, Scalable Reinforcement Learning for Multi-Agent Networked Systems, arXiv:1912.02906v3, p. 20, Lemma 14 (with eq. (28))

import Mathlib
import Definitions.Def_ScalableMARL_NetworkedMDP
import Definitions.Def_ScalableMARL_Assumptions
import Definitions.Def_ScalableMARL_SAC

namespace ScalableMARL

variable {n : ℕ} {S A : Fin n → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
  [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]

/-- **Lemma 14 (the critic error term `e¹`).** Qu, Wierman & Li, arXiv:1912.02906v3, p. 20,
Lemma 14. When `T` is large enough that
`C_a(δ/(2nM), T)/√(T + t₀) + C'_a/(T + t₀) ≤ 2cρ^{κ+1}/(1 − γ)²`, then with probability at least
`1 − δ/2`, `sup_{0 ≤ m ≤ M−1} ‖e¹(m)‖ ≤ 4cLρ^{κ+1}/(1 − γ)³`, where `e¹(m) = ĝ(m) − g(m)` (28).

**Formalization Note.** The standing hypotheses of Theorem 4 that the statement uses are assumed:
Assumptions 1–3, the bound `‖∇_{θ_i} log ζ_i‖ ≤ L_i` of Assumption 4, the step-size conditions on
`h, t₀`, and `δ ∈ (0, 1)`. The probability is under the law of the SAC run over `M` outer
iterations from an arbitrary `θ(0)` with any actor step `η`; the network has `n ≥ 1` agents (the
page divides by `n` in `δ/(2nM)`). -/
theorem lemma_14_e1_bound (M : NetMDP n S A) (pol : LocalPolicyClass n S A)
    (hn : 0 < n) (hM : M.Valid) (hpol : pol.IsDistribution)
    (rbar Sb Ab c ρ σ h t₀ η δ : ℝ) (L : Fin n → ℝ) (κ τ T Mo : ℕ)
    (hA1 : Assumption1 M rbar Sb Ab) (hA2 : Assumption2 M pol c ρ κ)
    (hA3 : Assumption3 M pol κ τ σ) (hA4 : LogGradBound pol L)
    (hh : 1 / σ * max 2 (1 / (1 - Real.sqrt M.γ)) ≤ h)
    (ht₀ : max (2 * h) (max (4 * σ * h) τ) ≤ t₀)
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hT : Ca M.γ rbar τ h σ (maxNbhdSize M.G κ) Sb Ab (δ / (2 * n * Mo)) T / Real.sqrt (T + t₀) +
        Ca' M.γ rbar τ h σ t₀ / (T + t₀) ≤ 2 * c * ρ ^ (κ + 1) / (1 - M.γ) ^ 2)
    (θ₀ : pol.Param) :
    1 - δ / 2 ≤ runProbOf M pol κ h t₀ η θ₀ {ω : Fin Mo → Episode S A T |
      ∀ m : Fin Mo,
        ‖ghat M pol κ h t₀ (thetaRun M pol κ h t₀ η θ₀ ω m) (ω m) -
            gvec M pol κ (thetaRun M pol κ h t₀ η θ₀ ω m) (ω m)‖ ≤
          4 * c * Lnorm L * ρ ^ (κ + 1) / (1 - M.γ) ^ 3} := by sorry

end ScalableMARL
