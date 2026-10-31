-- Prove2me | Theorems.Thm_ScalableMARL_theorem_5_critic_bound
-- name    : ScalableMARL.theorem_5_critic_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:48:10.945977+00:00
-- url     : https://prove2.me/theorems/a8ad5557-db9b-4900-97ba-52c28fedabb0
-- title:
--   Theorem 5 — the critic's error $\sup|Q_i^\theta-\hat Q_i^T|\le C_a/\sqrt{T+t_0}+C_a'/(T+t_0)+2c\rho^{\kappa+1}/(1-\gamma)^2$ with probability $\ge1-\delta$
-- statement:
--   Assume Assumptions 1, 2 and 3 (with $\bar r$, $S$, $A$, $c$, $\rho$, $\tau$, $\sigma$), and let the critic step sizes $\alpha_t=h/(t+t_0)$ satisfy
--   $$h\ge\frac1\sigma\max\Big(2,\frac{1}{1-\sqrt\gamma}\Big),\qquad t_0\ge\max(2h,4\sigma h,\tau).$$
--   Fix a policy $\theta$ (inside outer iteration $m$ of SAC, $\theta=\theta(m)$), and let $z(0),\dots,z(T)$ be an episode drawn under $\theta$ with $s(0)\sim\pi_0$. Let $\hat Q^T_i$ be the critic estimate (14) after $T$ steps. Then for each agent $i$ and each $\delta\in(0,1)$, with probability at least $1-\delta$,
--   $$\sup_{(s,a)\in\mathcal S\times\mathcal A}\big|Q_i^{\theta}(s,a)-\hat Q^T_i(s_{N_i^\kappa},a_{N_i^\kappa})\big|\le\frac{C_a}{\sqrt{T+t_0}}+\frac{C_a'}{T+t_0}+\frac{2c\rho^{\kappa+1}}{(1-\gamma)^2},$$
--   where $C_a=C_a(\delta,T)=\frac{6\bar\epsilon}{1-\sqrt\gamma}\sqrt{\frac{\tau h}{\sigma}[\log\frac{2\tau T^2}{\delta}+f(\kappa)\log SA]}$, $C_a'=\frac{2}{1-\sqrt\gamma}\max(\frac{16\bar\epsilon h\tau}{\sigma},\frac{2\bar r}{1-\gamma}(\tau+t_0))$ and $\bar\epsilon=\frac{4\bar r}{1-\gamma}+2\bar r$.
--
--   The bound splits into a transient that vanishes as $T\to\infty$ and a bias of order $\rho^{\kappa+1}$ caused by truncating the Q-function to the κ-hop neighbourhood.
--
--   **Formalization Note** The probability is the law of one episode under $\theta$; the supremum is stated pointwise for every $(s,a)$.
--
--   Differences from the source:
--   - generalization: the policy θ(m) inside outer iteration m → an arbitrary fixed policy θ; reason: the episode of iteration m is drawn under the fixed θ(m), so the page's statement is this one at θ = θ(m) (conditionally on the earlier iterations)
--   - encoding: expectations and probabilities over the networked MDP → finite sums over the finite state-action spaces and over episodes (Q_i^θ through the published one-step form r_i + γPV); reason: all spaces are finite, so these are the same numbers
--   - encoding: agents N = {1, …, n}, finite local sets S_i, A_i → Fin n and finite types; reason: Lean indexing
--   - reading: Assumption 3's P(z_{N_i^κ}(τ) = x | z(1) = z) ≥ σ → the (τ−1)-step law of the state-action chain from z puts mass ≥ σ on {z' : z'_{N_i^κ} = x}; reason: the chain is time homogeneous and z(1) to z(τ) is τ − 1 transitions
--   - reading: Definition 1 with κ unspecified, in Assumption 2 → the exponential decay property at the algorithm's κ; reason: κ is the algorithm's fixed parameter throughout; the proof uses only that κ
--   - encoding: the bounds S, A of Assumption 1 → real numbers Sb, Ab; reason: the page does not restrict them to integers; they enter only through log SA
-- source:
--   Qu, Wierman & Li, Scalable Reinforcement Learning for Multi-Agent Networked Systems, arXiv:1912.02906v3, p. 14, Theorem 5

import Mathlib
import Definitions.Def_ScalableMARL_NetworkedMDP
import Definitions.Def_ScalableMARL_Assumptions
import Definitions.Def_ScalableMARL_SAC

namespace ScalableMARL

variable {n : ℕ} {S A : Fin n → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
  [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]

/-- **Theorem 5 (critic error bound).** Qu, Wierman & Li, arXiv:1912.02906v3, p. 14, Theorem 5.
Under Assumptions 1, 2, 3, if `h ≥ (1/σ) max(2, 1/(1 − √γ))` and `t₀ ≥ max(2h, 4σh, τ)`, then
inside an outer iteration (policy `θ` fixed, one episode `z(0), …, z(T)` with `s(0) ∼ π₀`), for
each agent `i` and `δ ∈ (0, 1)`, with probability at least `1 − δ`,
`sup_{(s,a)} |Q_i^θ(s, a) − Q̂^T_i(s_{N_i^κ}, a_{N_i^κ})| ≤ C_a/√(T + t₀) + C'_a/(T + t₀) + 2cρ^{κ+1}/(1 − γ)²`,
with `C_a = C_a(δ, T)` and `C'_a` as in Theorem 4 and `Q̂^T_i` the critic (14) after `T` steps.

**Formalization Note.** Stated for an arbitrary fixed policy `θ` (the page's `θ(m)` inside outer
iteration `m`); the probability is the law `trajProb` of the episode under `θ`. `S`, `A` of
Assumption 1 are the reals `Sb`, `Ab`, and `f(κ) = max_i |N_i^κ|`. -/
theorem theorem_5_critic_bound (M : NetMDP n S A) (pol : LocalPolicyClass n S A)
    (hM : M.Valid) (hpol : pol.IsDistribution)
    (rbar Sb Ab c ρ σ h t₀ : ℝ) (κ τ T : ℕ)
    (hA1 : Assumption1 M rbar Sb Ab) (hA2 : Assumption2 M pol c ρ κ)
    (hA3 : Assumption3 M pol κ τ σ)
    (hh : 1 / σ * max 2 (1 / (1 - Real.sqrt M.γ)) ≤ h)
    (ht₀ : max (2 * h) (max (4 * σ * h) τ) ≤ t₀)
    (θ : pol.Param) (i : Fin n) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    1 - δ ≤ trajProbOf M pol θ {ep : Episode S A T | ∀ z : (∀ i, S i) × (∀ i, A i),
      |Qi M pol θ i z.1 z.2 - critic M κ i h t₀ ep T (restrictSA M.G κ i z)| ≤
        Ca M.γ rbar τ h σ (maxNbhdSize M.G κ) Sb Ab δ T / Real.sqrt (T + t₀) +
          Ca' M.γ rbar τ h σ t₀ / (T + t₀) + 2 * c * ρ ^ (κ + 1) / (1 - M.γ) ^ 2} := by sorry

end ScalableMARL
