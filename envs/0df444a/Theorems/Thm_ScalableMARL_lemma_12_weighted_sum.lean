-- Prove2me | Theorems.Thm_ScalableMARL_lemma_12_weighted_sum
-- name    : ScalableMARL.lemma_12_weighted_sum
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:47:33.846289+00:00
-- url     : https://prove2.me/theorems/2919d345-7d13-44ad-948c-3f9f7a284ef6
-- title:
--   Lemma 12 — $\sum_{k=\tau}^{t-1}b_{k,t}(k+t_0)^{-\omega}\le 1/(\sqrt\gamma\,(t+t_0)^\omega)$
-- statement:
--   Let $\sigma,\gamma\in(0,1)$, let $\alpha_k=h/(k+t_0)$, and let $\bar d_k$ be a sequence with $\sigma\le\bar d_k\le1$. Put $b_{k,t}=\alpha_k\bar d_k\prod_{\ell=k+1}^{t-1}(1-\alpha_\ell\bar d_\ell)$. If
--   $$\sigma h(1-\sqrt\gamma)\ge1,\qquad t_0\ge1,\qquad\alpha_0\le\tfrac12,$$
--   then for every $0<\omega\le1$ and all integers $\tau,t\ge0$,
--   $$\sum_{k=\tau}^{t-1}b_{k,t}\,\frac{1}{(k+t_0)^\omega}\le\frac{1}{\sqrt\gamma\,(t+t_0)^\omega}.$$
--
--   The lemma closes the induction in the proof of Theorem 5: applied with $\omega=\frac12$ and $\omega=1$ it shows that the critic's error bound $C_a/\sqrt{t+t_0}+C_a'/(t+t_0)$ propagates.
--
--   **Formalization Note** $(\cdot)^\omega$ is the real power `Real.rpow`; $\alpha_0=h/t_0$.
--
--   Differences from the source:
--   - generalization: d̄_k(z_{N_i^κ}), the marginal probability of a fixed local pair, with d̄_k ≥ σ → any real sequence d̄_k with σ ≤ d̄_k ≤ 1; reason: marginal probabilities bounded below by σ are such sequences, so the page's claim is the special case
--   - reading: σ, γ, τ unqualified in Lemma 12 → σ ∈ (0, 1), γ ∈ (0, 1), τ, t arbitrary natural numbers; reason: σ is that of Assumption 3 and γ the discount factor; the page does not restrict τ, t
-- source:
--   Qu, Wierman & Li, Scalable Reinforcement Learning for Multi-Agent Networked Systems, arXiv:1912.02906v3, p. 19, Lemma 12

import Mathlib
import Definitions.Def_ScalableMARL_StepSizes

namespace ScalableMARL

/-- **Lemma 12.** Qu, Wierman & Li, arXiv:1912.02906v3, p. 19, Lemma 12. Let `α_k = h/(k + t₀)` and
`b_{k,t} = α_k d̄_k ∏_{ℓ=k+1}^{t−1}(1 − α_ℓ d̄_ℓ)` with `d̄_k ≥ σ`. If `σh(1 − √γ) ≥ 1`, `t₀ ≥ 1` and
`α₀ ≤ 1/2`, then for every `0 < ω ≤ 1`,
`Σ_{k=τ}^{t−1} b_{k,t}/(k + t₀)^ω ≤ 1/(√γ (t + t₀)^ω)`.

**Formalization Note.** On the page `d̄_k = d̄_k(z_{N_i^κ})` is the marginal probability of a fixed
local pair, so `σ ≤ d̄_k ≤ 1`; here `d̄` is any real sequence with values in `[σ, 1]`. `σ ∈ (0, 1)`
(Assumption 3) and `γ ∈ (0, 1)` are the standing assumptions. The bound holds for all `τ, t ∈ ℕ`. -/
theorem lemma_12_weighted_sum (σ γ h t₀ ω : ℝ) (dbar : ℕ → ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hd : ∀ k, σ ≤ dbar k ∧ dbar k ≤ 1)
    (hσh : 1 ≤ σ * h * (1 - Real.sqrt γ)) (ht₀ : 1 ≤ t₀) (hα : h / t₀ ≤ 1 / 2)
    (hω0 : 0 < ω) (hω1 : ω ≤ 1) (τ t : ℕ) :
    ∑ k ∈ Finset.Ico τ t, bKT h t₀ dbar k t * (1 / ((k : ℝ) + t₀) ^ ω) ≤
      1 / (Real.sqrt γ * ((t : ℝ) + t₀) ^ ω) := by sorry

end ScalableMARL
