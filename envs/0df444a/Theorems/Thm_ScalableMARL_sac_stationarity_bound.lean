-- Prove2me | Theorems.Thm_ScalableMARL_sac_stationarity_bound
-- name    : ScalableMARL.sac_stationarity_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:48:33.122933+00:00
-- url     : https://prove2.me/theorems/63700d94-f371-4300-9d54-55dab0947dab
-- title:
--   Theorem 4 — with probability $\ge1-\delta$, SAC's weighted average of $\|\nabla J(\theta(m))\|^2$ is $\tilde O(1/\sqrt M)+O(\rho^{\kappa+1})$
-- statement:
--   Consider a network of $n\ge1$ agents with the networked MDP of §2.1 and a class of localized policies $\zeta_i^{\theta_i}$ (distributions on $\mathcal A_i$, positive and differentiable in $\theta_i$), and suppose Assumptions 1–4 hold: $0\le r_i\le\bar r$, $|\mathcal S_i|\le S$, $|\mathcal A_i|\le A$; the $(c,\rho)$-exponential decay property at the hop count $\kappa$ with $c,\rho>0$ and $\rho\le\gamma$; sufficient local exploration with an integer $\tau\ge1$ and $\sigma\in(0,1)$; $\|\nabla_{\theta_i}\log\zeta_i^{\theta_i}(a_i\mid s_i)\|\le L_i$, $L=\sqrt{\sum_iL_i^2}$, and $\nabla J$ is $L'$-Lipschitz.
--
--   Let $\delta\in(0,1)$ and $M\ge3$. Suppose the critic step size $\alpha_t=h/(t+t_0)$ satisfies
--   $$h\ge\frac1\sigma\max\Big(2,\frac{1}{1-\sqrt\gamma}\Big),\qquad t_0\ge\max(2h,4\sigma h,\tau),$$
--   the actor step size is $\eta_m=\eta/\sqrt{m+1}$ with $0<\eta\le\frac{1}{4L'}$, and the inner loop length $T$ satisfies $T+1\ge\log_\gamma\frac{c(1-\gamma)}{\bar r}+(\kappa+1)\log_\gamma\rho$ and
--   $$\frac{C_a(\frac{\delta}{2nM},T)}{\sqrt{T+t_0}}+\frac{C_a'}{T+t_0}\le\frac{2c\rho^{\kappa+1}}{(1-\gamma)^2},\tag{12}$$
--   where $C_a(\delta,T)=\frac{6\bar\epsilon}{1-\sqrt\gamma}\sqrt{\frac{\tau h}{\sigma}[\log\frac{2\tau T^2}{\delta}+f(\kappa)\log SA]}$, $C_a'=\frac{2}{1-\sqrt\gamma}\max(\frac{16\bar\epsilon h\tau}{\sigma},\frac{2\bar r}{1-\gamma}(\tau+t_0))$, $\bar\epsilon=\frac{4\bar r}{1-\gamma}+2\bar r$ and $f(\kappa)=\max_i|N_i^\kappa|$. Run Scalable Actor Critic (Algorithm 1) for $M$ outer iterations from any $\theta(0)$. Then, with probability at least $1-\delta$,
--   $$\frac{\sum_{m=0}^{M-1}\eta_m\|\nabla J(\theta(m))\|^2}{\sum_{m=0}^{M-1}\eta_m}\le\frac{\frac{2\bar r}{\eta(1-\gamma)}+\frac{8\bar r^2L^2}{(1-\gamma)^4}\sqrt{\log M\log\frac4\delta}+\frac{96\bar r^2L'L^2}{(1-\gamma)^4}\eta\log M}{\sqrt{M+1}}+\frac{12L^2c\bar r}{(1-\gamma)^5}\rho^{\kappa+1}.\tag{13}$$
--
--   The first term vanishes at rate $\tilde O(1/\sqrt M)$ and the second is the bias of truncating the Q-functions to κ-hop neighbourhoods, of order $\rho^{\kappa+1}$. So SAC finds an $O(\rho^{\kappa+1})$-approximate stationary point of $J$ while every agent only stores tables over its κ-hop neighbourhood, whose size depends on $f(\kappa)$ and not on $n$.
--
--   **Formalization Note** The probability is under the law of the SAC run: episode $m$ is drawn, with a fresh $s(0)\sim\pi_0$, under the policy $\theta(m)$ computed by the algorithm from the earlier episodes. $\log_\gamma$ is `Real.logb γ`. $\eta\le1/(4L')$ is written $4L'\eta\le1$.
--
--   Differences from the source:
--   - generalization: η ≤ 1/(4L′) → 4L′η ≤ 1 with L′ ≥ 0; reason: equivalent for L′ > 0, and it also covers L′ = 0, where 1/(4L′) is undefined
--   - encoding: η unqualified → η > 0; reason: η_m is a step size and the left side of (13) divides by Σ η_m
--   - encoding: ∇J is L′-Lipschitz → L′ ≥ 0 and ‖∇J(θ) − ∇J(θ′)‖ ≤ L′‖θ − θ′‖ for all θ, θ′; reason: definition of an L′-Lipschitz map, whose constant is nonnegative
--   - encoding: c, ρ unqualified → c > 0 and ρ > 0; reason: presupposed by log_γ(c(1−γ)/r̄) and log_γ ρ; excludes only cases where the condition on T is undefined
--   - encoding: a network of agents N = {1, …, n} → n ≥ 1; reason: the page divides by n in δ/(2nM); excludes only the case where (12) is undefined
--   - encoding: ∇_{θ_i} log ζ_i^{θ_i}(a_i|s_i) used as given → ζ_i^{θ_i}(a_i|s_i) > 0 and θ_i ↦ ζ_i^{θ_i}(a_i|s_i) differentiable; reason: presupposed for the gradient of the logarithm in Assumption 4 to exist; excludes only cases where Assumption 4 is undefined
--   - reading: Assumption 3's P(z_{N_i^κ}(τ) = x | z(1) = z) ≥ σ → the (τ−1)-step law of the state-action chain from z puts mass ≥ σ on {z' : z'_{N_i^κ} = x}; reason: the chain is time homogeneous and z(1) to z(τ) is τ − 1 transitions
--   - reading: Definition 1 with κ unspecified, in Assumption 2 → the exponential decay property at the algorithm's κ; reason: κ is the algorithm's fixed parameter throughout; the proof uses only that κ
--   - reading: localized policies parameterized by θ_i (parameter space unnamed, norms Euclidean) → θ_i ∈ ℝ^{d_i}, θ in PiLp 2 with the Euclidean norm of the whole tuple; reason: the page differentiates in θ and uses Euclidean norms
--   - encoding: expectations and probabilities over the networked MDP and the algorithm → finite sums over the finite state-action spaces and over runs of M episodes (Q_i^θ through the published one-step form r_i + γPV; run probability ∏_m P_{θ(m)}(episode m)); reason: all spaces are finite, so these are the same numbers
--   - encoding: agents N = {1, …, n}, finite local sets S_i, A_i → Fin n and finite types; reason: Lean indexing
--   - encoding: the bounds S, A of Assumption 1 → real numbers Sb, Ab; reason: the page does not restrict them to integers; they enter only through log SA
-- source:
--   Qu, Wierman & Li, Scalable Reinforcement Learning for Multi-Agent Networked Systems, arXiv:1912.02906v3, p. 12, Theorem 4, eqs. (12)–(13)

import Mathlib
import Definitions.Def_ScalableMARL_NetworkedMDP
import Definitions.Def_ScalableMARL_Assumptions
import Definitions.Def_ScalableMARL_SAC

namespace ScalableMARL

variable {n : ℕ} {S A : Fin n → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
  [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]

/-- **Theorem 4 (SAC finds an `O(ρ^{κ+1})`-stationary point).** Qu, Wierman & Li, *Scalable
Reinforcement Learning for Multi-Agent Networked Systems*, arXiv:1912.02906v3, p. 12, Theorem 4.
Under Assumptions 1, 2, 3 and 4, for any `δ ∈ (0, 1)` and `M ≥ 3`, suppose the critic step size
`α_t = h/(t + t₀)` satisfies `h ≥ (1/σ) max(2, 1/(1 − √γ))`, `t₀ ≥ max(2h, 4σh, τ)`, the actor
step size is `η_m = η/√(m + 1)` with `η ≤ 1/(4L')`, and `T` satisfies
`T + 1 ≥ log_γ(c(1 − γ)/r̄) + (κ + 1) log_γ ρ` and (12)
`C_a(δ/(2nM), T)/√(T + t₀) + C'_a/(T + t₀) ≤ 2cρ^{κ+1}/(1 − γ)²`.
Then, with probability at least `1 − δ`, (13):
`Σ_{m<M} η_m ‖∇J(θ(m))‖² / Σ_{m<M} η_m ≤
 [2r̄/(η(1 − γ)) + (8r̄²L²/(1 − γ)⁴) √(log M log(4/δ)) + (96r̄²L'L²/(1 − γ)⁴) η log M]/√(M + 1)
 + (12L²cr̄/(1 − γ)⁵) ρ^{κ+1}`.

**Formalization Note.** The probability is under the law of the SAC run (Algorithm 1) over `M`
outer iterations from an arbitrary `θ(0)`, each episode drawn under the current `θ(m)`.
`η > 0`, `η ≤ 1/(4L')` is written `4L'η ≤ 1` with a Lipschitz constant `L' ≥ 0`; `c, ρ > 0`
(presupposed by `log_γ`); the policies are positive and differentiable in their parameters
(presupposed by Assumption 4). The network has `n ≥ 1` agents (the page divides by `n` in
`δ/(2nM)`). `S`, `A` of Assumption 1 are the reals `Sb`, `Ab`. -/
theorem sac_stationarity_bound (M : NetMDP n S A) (pol : LocalPolicyClass n S A)
    (hn : 0 < n) (hM : M.Valid) (hpol : pol.IsDistribution) (hpd : pol.PositiveDifferentiable)
    (rbar Sb Ab c ρ σ h t₀ η L' δ : ℝ) (L : Fin n → ℝ) (κ τ T Mo : ℕ)
    (hA1 : Assumption1 M rbar Sb Ab) (hc : 0 < c) (hρ : 0 < ρ)
    (hA2 : Assumption2 M pol c ρ κ) (hA3 : Assumption3 M pol κ τ σ)
    (hA4 : LogGradBound pol L) (hA4' : GradLipschitz M pol L')
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hMo : 3 ≤ Mo)
    (hh : 1 / σ * max 2 (1 / (1 - Real.sqrt M.γ)) ≤ h)
    (ht₀ : max (2 * h) (max (4 * σ * h) τ) ≤ t₀)
    (hη : 0 < η) (hηL : 4 * L' * η ≤ 1)
    (hT1 : Real.logb M.γ (c * (1 - M.γ) / rbar) + (κ + 1) * Real.logb M.γ ρ ≤ T + 1)
    (hT2 : Ca M.γ rbar τ h σ (maxNbhdSize M.G κ) Sb Ab (δ / (2 * n * Mo)) T / Real.sqrt (T + t₀) +
        Ca' M.γ rbar τ h σ t₀ / (T + t₀) ≤ 2 * c * ρ ^ (κ + 1) / (1 - M.γ) ^ 2)
    (θ₀ : pol.Param) :
    1 - δ ≤ runProbOf M pol κ h t₀ η θ₀ {ω : Fin Mo → Episode S A T |
      (∑ m ∈ Finset.range Mo,
          actorStep η m * ‖gradient (J M pol) (thetaRun M pol κ h t₀ η θ₀ ω m)‖ ^ 2) /
        (∑ m ∈ Finset.range Mo, actorStep η m) ≤
      (2 * rbar / (η * (1 - M.γ)) +
          8 * rbar ^ 2 * Lnorm L ^ 2 / (1 - M.γ) ^ 4 *
            Real.sqrt (Real.log Mo * Real.log (4 / δ)) +
          96 * rbar ^ 2 * L' * Lnorm L ^ 2 / (1 - M.γ) ^ 4 * η * Real.log Mo) /
        Real.sqrt (Mo + 1) +
      12 * Lnorm L ^ 2 * c * rbar / (1 - M.γ) ^ 5 * ρ ^ (κ + 1)} := by sorry

end ScalableMARL
