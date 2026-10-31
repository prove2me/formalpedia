-- Prove2me | Theorems.Thm_ScalableMARL_lemma_17_projected_bellman
-- name    : ScalableMARL.lemma_17_projected_bellman
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:48:18.780129+00:00
-- url     : https://prove2.me/theorems/8579ea0e-af6e-4ecc-bcf1-931e59861e9c
-- title:
--   Lemma 17 — $g_d=\Pi_dT_D\Phi$ is a $\gamma$-contraction whose fixed point is within $c\rho^{\kappa+1}/(1-\gamma)$ of $Q_i^\theta$
-- statement:
--   Consider the networked MDP with valid data, localized policies that are distributions, and the $(c,\rho)$-exponential decay property at hop count $\kappa$. Fix a policy $\theta$, an agent $i$, and a distribution $d$ on the state-action pairs $\mathcal Z$ whose marginal on $z_{N_i^\kappa}$ is non-zero for every local pair. With $\Phi$, $P$, $\bar A_d$, $\bar b_d$, $D$, $\Pi_d$, $T_D$ and $g_d$ as in the module `ProjectedBellman`:
--
--   1. for every $\hat Q_i\in\mathbb R^{\mathcal Z_{N_i^\kappa}}$,
--   $$\bar A_d\hat Q_i+\bar b_d=-D\hat Q_i+D\,g_d(\hat Q_i);$$
--   2. $D=\Phi^\top\operatorname{diag}(d)\Phi$ is the diagonal matrix whose $z_{N_i^\kappa}$-th entry is the marginal probability of $z_{N_i^\kappa}$ under $d$;
--   3. $g_d$ is a $\gamma$-contraction in the infinity norm: $\|g_d(Q)-g_d(Q')\|_\infty\le\gamma\|Q-Q'\|_\infty$;
--   4. $g_d$ has a unique fixed point $\hat Q_i^d$, and
--   $$\sup_{z\in\mathcal Z}\big|\hat Q_i^d(z_{N_i^\kappa})-Q_i^\theta(z)\big|=\|\Phi\hat Q_i^d-Q_i^\theta\|_\infty\le\frac{c\rho^{\kappa+1}}{1-\gamma}.$$
--
--   This is the deterministic core of the critic analysis: the expected TD update is a preconditioned fixed-point iteration of $g_d$, whose fixed point is close to the true Q-function by exponential decay.
--
--   **Formalization Note** The norm on $\mathbb R^{\mathcal Z_{N_i^\kappa}}$ is Mathlib's sup norm on functions, i.e. $\|\cdot\|_\infty$; (42) is stated pointwise in $z$. $Q^*_i$ on the page is the true Q-function $Q_i^\theta$.
--
--   Differences from the source:
--   - encoding: expectations over the networked MDP → finite sums over the finite state and action spaces (Q_i^θ through the published one-step form r_i + γPV); reason: all spaces are finite, so these are the same numbers
--   - encoding: agents N = {1, …, n}, finite local sets S_i, A_i → Fin n and finite types; reason: Lean indexing
--   - reading: Lemma 17 states (42) without naming its hypothesis → the (c, ρ)-exponential decay property at κ is assumed; reason: it is the standing Assumption 2 of §4.1, where Lemma 17 is used, and c, ρ in (42) refer to it
--   - encoding: "distribution d on Z" → d ≥ 0 and Σ_z d(z) = 1; reason: definition of a distribution on a finite set
--   - encoding: ‖·‖_∞ and "unique fixed point" → Mathlib's sup norm on Z_{N_i^κ} → ℝ, and ∃ Q̂ with g_d(Q̂) = Q̂ such that every fixed point equals Q̂; reason: same statements
-- source:
--   Qu, Wierman & Li, Scalable Reinforcement Learning for Multi-Agent Networked Systems, arXiv:1912.02906v3, p. 29, Lemma 17, eqs. (40)–(42)

import Mathlib
import Definitions.Def_ScalableMARL_NetworkedMDP
import Definitions.Def_ScalableMARL_ProjectedBellman

namespace ScalableMARL

open Matrix

variable {n : ℕ} {S A : Fin n → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
  [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]

/-- **Lemma 17 (the projected Bellman operator).** Qu, Wierman & Li, arXiv:1912.02906v3, p. 29,
Lemma 17, (40)–(42). Fix a policy `θ` and an agent `i`, and let `d` be a distribution on the
state-action pairs `Z` whose marginal on `z_{N_i^κ}` is non-zero for every local pair. Then
`Ā_d Q̂_i + b̄_d = −D Q̂_i + D g_d(Q̂_i)` for every `Q̂_i`, where `D = Φᵀ diag(d) Φ` is the diagonal
matrix of the marginals of `d`, `g_d(Q̂_i) = Π_d T_D Φ Q̂_i`; `g_d` is a `γ`-contraction in the
infinity norm; it has a unique fixed point `Q̂_i^d`, and
`sup_z |Q̂_i^d(z_{N_i^κ}) − Q_i^θ(z)| ≤ c ρ^{κ+1}/(1 − γ)`.

**Formalization Note.** The norm on `Z_{N_i^κ} → ℝ` is Mathlib's sup norm, i.e. `‖·‖_∞`.
`Q*_i` of the page is `Q_i^θ`. The `(c, ρ)`-exponential decay property is the standing
Assumption 2 of §4.1 (needed for (42)). -/
theorem lemma_17_projected_bellman (M : NetMDP n S A) (pol : LocalPolicyClass n S A)
    (hM : M.Valid) (hpol : pol.IsDistribution) (c ρ : ℝ) (κ : ℕ)
    (hED : ExpDecay M pol c ρ κ) (θ : pol.Param) (i : Fin n)
    (d : ((∀ i, S i) × (∀ i, A i)) → ℝ) (hd0 : ∀ z, 0 ≤ d z) (hd1 : ∑ z, d z = 1)
    (hmarg : ∀ x : LocSA M.G κ i S A,
      ∑ z ∈ Finset.univ.filter (fun z => restrictSA M.G κ i z = x), d z ≠ 0) :
    (∀ Qh : LocSA M.G κ i S A → ℝ,
      Abar M pol θ κ i d *ᵥ Qh + bbar M κ i d =
        -(Dmat M κ i d *ᵥ Qh) + Dmat M κ i d *ᵥ gD M pol θ κ i d Qh) ∧
    Dmat M κ i d =
      diagonal (fun x => ∑ z ∈ Finset.univ.filter (fun z => restrictSA M.G κ i z = x), d z) ∧
    (∀ Q Q' : LocSA M.G κ i S A → ℝ,
      ‖gD M pol θ κ i d Q - gD M pol θ κ i d Q'‖ ≤ M.γ * ‖Q - Q'‖) ∧
    ∃ Qd : LocSA M.G κ i S A → ℝ, gD M pol θ κ i d Qd = Qd ∧
      (∀ Q, gD M pol θ κ i d Q = Q → Q = Qd) ∧
      ∀ z : (∀ i, S i) × (∀ i, A i),
        |Qd (restrictSA M.G κ i z) - Qi M pol θ i z.1 z.2| ≤ c * ρ ^ (κ + 1) / (1 - M.γ) := by sorry

end ScalableMARL
