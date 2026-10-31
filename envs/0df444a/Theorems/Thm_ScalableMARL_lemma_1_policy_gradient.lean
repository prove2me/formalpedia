-- Prove2me | Theorems.Thm_ScalableMARL_lemma_1_policy_gradient
-- name    : ScalableMARL.lemma_1_policy_gradient
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:47:38.519187+00:00
-- url     : https://prove2.me/theorems/c013ac4d-938b-4de7-996f-09e44d368ae2
-- title:
--   Lemma 1 — policy gradient theorem $\nabla J(\theta)=\frac{1}{1-\gamma}\mathbb E_{s\sim\pi^\theta,a\sim\zeta^\theta}[Q^\theta(s,a)\nabla\log\zeta^\theta(a|s)]$
-- statement:
--   Consider the networked MDP with valid data and a class of localized policies $\zeta_i^{\theta_i}$ that are distributions on $\mathcal A_i$, positive and differentiable in $\theta_i$. Let $\pi^\theta(s)=(1-\gamma)\sum_{t\ge0}\gamma^t\pi^\theta_t(s)$, where $\pi^\theta_t$ is the distribution of $s(t)$ under the fixed policy $\theta$ when $s(0)\sim\pi_0$. Then $J$ is differentiable at every $\theta$ and
--
--   $$\nabla J(\theta)=\frac{1}{1-\gamma}\,\mathbb E_{s\sim\pi^\theta,\,a\sim\zeta^\theta(\cdot\mid s)}\Big[Q^\theta(s,a)\,\nabla\log\zeta^\theta(a\mid s)\Big].$$
--
--   This is the policy gradient theorem of Sutton et al. (2000) in the networked setting. It expresses the gradient of the objective through the global Q-function, which is an exponentially large table; the rest of the paper approximates it by truncated Q-functions.
--
--   **Formalization Note** The conclusion is `HasGradientAt J (…) θ` on the Euclidean parameter space; the expectation is a finite sum, and $\nabla\log\zeta^\theta(a\mid s)$ is the gradient of $\theta'\mapsto\log\zeta^{\theta'}(a\mid s)$ at $\theta$.
--
--   Differences from the source:
--   - encoding: expectations over the networked MDP → finite sums over the finite state and action spaces (Q^θ through the published one-step form r + γPV, J and π_t^θ through the time-t state law); reason: all spaces are finite, so these are the same numbers
--   - encoding: agents N = {1, …, n}, finite local sets S_i, A_i → Fin n and finite types; reason: Lean indexing
--   - reading: localized policies parameterized by θ_i (parameter space unnamed, norms Euclidean) → θ_i ∈ ℝ^{d_i}, θ in PiLp 2 with the Euclidean norm of the whole tuple; reason: the page differentiates in θ and uses Euclidean norms
--   - encoding: ∇ log ζ^θ(a|s) used as given → ζ_i^{θ_i}(a_i|s_i) > 0 and θ_i ↦ ζ_i^{θ_i}(a_i|s_i) differentiable; reason: presupposed for the gradient of the logarithm to exist; excludes only cases where (8) is undefined
--   - encoding: ∇J(θ) = (8) → HasGradientAt J (8) θ; reason: this is what the identity asserts, including that ∇J(θ) exists
-- source:
--   Qu, Wierman & Li, Scalable Reinforcement Learning for Multi-Agent Networked Systems, arXiv:1912.02906v3, p. 8, Lemma 1, eq. (8)

import Mathlib
import Definitions.Def_ScalableMARL_NetworkedMDP

namespace ScalableMARL

variable {n : ℕ} {S A : Fin n → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
  [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]

/-- **Lemma 1 (policy gradient theorem, Sutton et al. 2000).** Qu, Wierman & Li, *Scalable
Reinforcement Learning for Multi-Agent Networked Systems*, arXiv:1912.02906v3, p. 8, Lemma 1, (8):
with `π^θ(s) = (1 − γ) Σ_{t≥0} γ^t π_t^θ(s)`,
`∇J(θ) = (1/(1 − γ)) E_{s∼π^θ, a∼ζ^θ(·|s)}[Q^θ(s, a) ∇ log ζ^θ(a | s)]`.

**Formalization Note.** Stated as `HasGradientAt` (so `J` is differentiable at every `θ`, and
`gradient J θ` is the right-hand side) on the parameter space `PiLp 2 (Π_i ℝ^{d_i})`. The
policies are positive and differentiable in their parameters (what Assumption 4 presupposes). -/
theorem lemma_1_policy_gradient (M : NetMDP n S A) (pol : LocalPolicyClass n S A)
    (hM : M.Valid) (hpol : pol.IsDistribution) (hpd : pol.PositiveDifferentiable)
    (θ : pol.Param) :
    HasGradientAt (J M pol)
      ((1 - M.γ)⁻¹ • ∑ s, ∑ a, (visitation M pol θ s * pol.joint θ s a * Qglob M pol θ s a) •
        gradient (fun θ' : pol.Param => Real.log (pol.joint θ' s a)) θ) θ := by sorry

end ScalableMARL
