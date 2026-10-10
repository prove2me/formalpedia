-- Prove2me | Theorems.Thm_PosteriorSamplingRL_Regret_eq6_bellman_error
-- name    : PosteriorSamplingRL.Regret.eq6_bellman_error
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T21:04:53.766991+00:00
-- url     : https://prove2.me/theorems/1ea47781-efc5-43a2-914d-ca5b207e849c
-- title:
--   (6), §5.1, p. 6 — E[Δ̃_k | M*, M_k] = E[Σ_i (T^k_{µ_k(·,i)} − T^*_{µ_k(·,i)}) V^k_{µ_k,i+1}(s_{t_k+i}) | M*, M_k]
-- statement:
--   Consider a PSRL run with $M^*\sim f$. For an episode $k$ write $\mathcal T^k=\mathcal T^{M_k}$, $\mathcal T^*=\mathcal T^{M^*}$ and $V^k_{\mu_k,i}=V^{M_k}_{\mu_k,i}$, and let $s_{k,1},\dots,s_{k,\tau}$ be the states visited in episode $k$. Then
--   $$
--   \mathbb E\big[\tilde\Delta_k\,\big|\,M^*,M_k\big]=\mathbb E\Big[\sum_{i=1}^\tau\big(\mathcal T^k_{\mu_k(\cdot,i)}-\mathcal T^*_{\mu_k(\cdot,i)}\big)V^k_{\mu_k,i+1}(s_{k,i})\,\Big|\,M^*,M_k\Big]\qquad\text{almost surely.}
--   $$
--
--   The right-hand side involves only one-step Bellman errors of the sampled MDP along the states that the agent actually visits; this is what makes the gap $\tilde\Delta_k$ controllable by confidence sets.
--
--   **Formalization Note** The page evaluates step $i$ at $s_{t_k+i}$, while its own conventions ($t_k=(k-1)\tau+1$ is the first time of episode $k$, $a_t=\mu(s_t,t-t_k)$) make the $i$-th state of the episode $s_{t_k+i-1}$; the Lean statement evaluates the $i$-th Bellman error at the $i$-th state of the episode (`st k j`, 0-based $j=i-1$). Conditioning is on $\sigma(M^*)\vee\sigma(M_k)$.
-- source:
--   arXiv:1306.0940v5, §5.1, (6), p. 6

import Mathlib
import Definitions.Def_PosteriorSamplingRL_Regret_Run

open MeasureTheory ProbabilityTheory

namespace PosteriorSamplingRL.Regret

/-- (6), §5.1 (arXiv:1306.0940v5, p. 6):
`E[Δ̃_k | M*, M_k] = E[∑_{i=1}^τ (T^k_{µ_k(·,i)} − T^*_{µ_k(·,i)}) V^k_{µ_k,i+1}(s_{t_k+i}) | M*, M_k]`,
in 0-based steps: the `j`-th Bellman error is evaluated at the `j`-th state of episode `k`. -/
theorem eq6_bellman_error (S A τ : ℕ) (hS : 1 ≤ S) (hA : 1 ≤ A) (hτ : 1 ≤ τ)
    (Θ : Type) [MeasurableSpace Θ] (F : MDPFamily S A Θ) (ρ : Fin S → ℝ) (hρ : IsDist ρ)
    (f : Measure Θ) (sel : Θ → Policy S A τ) (hsel : ∀ θ, IsOptimal F θ (sel θ))
    (hsel_meas : Measurable sel)
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R : PSRLRun F ρ f sel μ) (k : ℕ) :
    μ[R.Δtilde k | R.pairSigma k]
      =ᵐ[μ] μ[fun ω => ∑ j : Fin τ, R.bellmanErr k j ω | R.pairSigma k] := by sorry

end PosteriorSamplingRL.Regret
