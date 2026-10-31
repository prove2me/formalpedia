-- Prove2me | Theorems.Thm_ScalableMARL_lemma_3_truncation
-- name    : ScalableMARL.lemma_3_truncation
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:47:33.555738+00:00
-- url     : https://prove2.me/theorems/1653a303-4529-4366-aa04-b834f4f48aa7
-- title:
--   Lemma 3 — truncated Q-functions are $c\rho^{\kappa+1}$-accurate, and the truncated policy gradient is $\frac{cL_i}{1-\gamma}\rho^{\kappa+1}$-accurate
-- statement:
--   Consider the networked MDP with valid data and localized policies that are distributions, and suppose the $(c,\rho)$-exponential decay property (Definition 1) holds at hop count $\kappa$: for every policy $\theta$, every $i$ and all $z,z'$ agreeing on $N_i^\kappa$, $|Q_i^\theta(z)-Q_i^\theta(z')|\le c\rho^{\kappa+1}$. Then:
--
--   1. Every truncated Q-function $\hat Q_i^\theta$ of the form (9)–(10) satisfies
--   $$\sup_{(s,a)\in\mathcal S\times\mathcal A}\big|\hat Q_i^\theta(s_{N_i^\kappa},a_{N_i^\kappa})-Q_i^\theta(s,a)\big|\le c\rho^{\kappa+1}.$$
--   2. If the policies are positive and differentiable in their parameters, fix $i$ and truncated Q-functions $\hat Q_j^\theta$, $j\in N_i^\kappa$, of the form (9) (each with its own weights), and define the truncated policy gradient (11)
--   $$\hat h_i(\theta)=\frac{1}{1-\gamma}\,\mathbb E_{s\sim\pi^\theta,a\sim\zeta^\theta(\cdot\mid s)}\Big[\frac1n\nabla_{\theta_i}\log\zeta_i^{\theta_i}(a_i\mid s_i)\sum_{j\in N_i^\kappa}\hat Q_j^\theta(s_{N_j^\kappa},a_{N_j^\kappa})\Big].$$
--   If $\|\nabla_{\theta_i}\log\zeta_i^{\theta_i}(a_i\mid s_i)\|\le L_i$ for all $a_i,s_i$, then
--   $$\big\|\hat h_i(\theta)-\nabla_{\theta_i}J(\theta)\big\|\le\frac{cL_i}{1-\gamma}\rho^{\kappa+1}.$$
--
--   This is the key observation of the paper: under exponential decay, a table indexed only by the κ-hop neighbourhood approximates $Q_i^\theta$, and gradients assembled from such tables approximate the true policy gradient.
--
--   **Formalization Note** In (9) the weights are indexed by the global pairs $z$ with $z_{N_i^\kappa}=x$, in bijection with the tuples $z_{N_{-i}^\kappa}$ of the page. $\nabla_{\theta_i}J(\theta)$ is the $i$-th block of the gradient of $J$ on the Euclidean parameter space.
--
--   Differences from the source:
--   - encoding: expectations over the networked MDP → finite sums over the finite state and action spaces (Q_i^θ through the published one-step form r_i + γPV, π^θ through the time-t state law); reason: all spaces are finite, so these are the same numbers
--   - encoding: agents N = {1, …, n}, finite local sets S_i, A_i → Fin n and finite types; reason: Lean indexing
--   - reading: localized policies parameterized by θ_i (parameter space unnamed, norms Euclidean) → θ_i ∈ ℝ^{d_i}, θ in PiLp 2 with the Euclidean norm of the whole tuple; reason: the page differentiates in θ and uses Euclidean norms
--   - encoding: ∇_{θ_i} log ζ_i^{θ_i}(a_i|s_i) used as given in (b) → in clause (b), ζ_i^{θ_i}(a_i|s_i) > 0 and θ_i ↦ ζ_i^{θ_i}(a_i|s_i) differentiable; reason: presupposed for the gradient of the logarithm to exist; excludes only cases where (11) and ∇J are undefined
--   - encoding: weights w_i(s_{N_{−i}^κ}, a_{N_{−i}^κ}; s_{N_i^κ}, a_{N_i^κ}) → weights on the global pairs z with z_{N_i^κ} = x; reason: the two index sets are in bijection
--   - reading: Definition 1 with κ unspecified → the exponential decay property at the κ of the truncation; reason: κ is the hop count of the truncated Q-functions throughout
-- source:
--   Qu, Wierman & Li, Scalable Reinforcement Learning for Multi-Agent Networked Systems, arXiv:1912.02906v3, p. 9, Lemma 3 (a)–(b), eqs. (9)–(11)

import Mathlib
import Definitions.Def_ScalableMARL_NetworkedMDP

namespace ScalableMARL

variable {n : ℕ} {S A : Fin n → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
  [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]

/-- **Lemma 3 (truncated Q-functions and the truncated policy gradient).** Qu, Wierman & Li,
arXiv:1912.02906v3, p. 9, Lemma 3. Under the `(c, ρ)`-exponential decay property (Definition 1):
(a) every truncated Q-function `Q̂_i^θ` of the form (9)–(10) satisfies
`sup_{(s,a)} |Q̂_i^θ(s_{N_i^κ}, a_{N_i^κ}) − Q_i^θ(s, a)| ≤ c ρ^{κ+1}`;
(b) for an agent `i`, truncated Q-functions `Q̂_j^θ` of the form (9) (each with its own
weights) and the truncated policy gradient (11)
`ĥ_i(θ) = (1/(1 − γ)) E_{s∼π^θ, a∼ζ^θ(·|s)}[(1/n) ∇_{θ_i} log ζ_i^{θ_i}(a_i|s_i)
Σ_{j ∈ N_i^κ} Q̂_j^θ(s_{N_j^κ}, a_{N_j^κ})]`, if `‖∇_{θ_i} log ζ_i^{θ_i}(a_i|s_i)‖ ≤ L_i` for all
`a_i, s_i`, then `‖ĥ_i(θ) − ∇_{θ_i} J(θ)‖ ≤ (c L_i/(1 − γ)) ρ^{κ+1}`.

**Formalization Note.** `∇_{θ_i} J(θ)` is the `i`-th block of `gradient (J M pol) θ`. Only clause (b)
assumes that the policies are positive and differentiable in their parameters (what its
`∇_{θ_i} log ζ_i` presupposes); clause (a) involves no gradient. -/
theorem lemma_3_truncation (M : NetMDP n S A) (pol : LocalPolicyClass n S A)
    (hM : M.Valid) (hpol : pol.IsDistribution)
    (c ρ : ℝ) (κ : ℕ) (hED : ExpDecay M pol c ρ κ) :
    (∀ (θ : pol.Param) (i : Fin n) (Qh : LocSA M.G κ i S A → ℝ), IsTruncatedQ M pol θ κ i Qh →
        ∀ z : (∀ i, S i) × (∀ i, A i),
          |Qh (restrictSA M.G κ i z) - Qi M pol θ i z.1 z.2| ≤ c * ρ ^ (κ + 1)) ∧
    (pol.PositiveDifferentiable →
      ∀ (θ : pol.Param) (i : Fin n) (Qh : ∀ j, LocSA M.G κ j S A → ℝ),
        (∀ j ∈ nbhd M.G κ i, IsTruncatedQ M pol θ κ j (Qh j)) → ∀ Li : ℝ,
        (∀ s a, ‖pol.logGrad i (θ i) s a‖ ≤ Li) →
          ‖(1 - M.γ)⁻¹ • ∑ s, ∑ a,
              (visitation M pol θ s * pol.joint θ s a *
                ((n : ℝ)⁻¹ * ∑ j ∈ nbhd M.G κ i, Qh j (restrictSA M.G κ j (s, a)))) •
                pol.logGrad i (θ i) (s i) (a i)
            - gradient (J M pol) θ i‖ ≤ c * Li / (1 - M.γ) * ρ ^ (κ + 1)) := by sorry

end ScalableMARL
