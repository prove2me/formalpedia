-- Prove2me | Theorems.Thm_PosteriorSamplingRL_Regret_theorem2_regret_equivalence
-- name    : PosteriorSamplingRL.Regret.theorem2_regret_equivalence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T21:02:57.42799+00:00
-- url     : https://prove2.me/theorems/988fee40-3540-4d6b-811d-61419b5f9bb8
-- title:
--   Theorem 2, (4), p. 5 — regret equivalence: E[Σ_{k=1}^m Δ_k] = E[Σ_{k=1}^m Δ̃_k]
-- statement:
--   Consider a PSRL run in which $M^*$ has the prior distribution $f$. Let $\Delta_k$ be the regret of episode $k$ and $\tilde\Delta_k=\sum_s\rho(s)\big(V^{M_k}_{\mu_k,1}(s)-V^{M^*}_{\mu_k,1}(s)\big)$ the gap between the value of $\mu_k$ in the sampled MDP and in the true MDP. Then for every number of episodes $m$,
--   $$
--   \mathbb E\Big[\sum_{k=1}^m\Delta_k\Big]=\mathbb E\Big[\sum_{k=1}^m\tilde\Delta_k\Big].
--   $$
--
--   The regret involves the unobserved optimal policy $\mu^*$; the gap $\tilde\Delta_k$ involves only the policy the agent actually follows, so the theorem reduces the analysis to quantities that can be estimated from data.
--
--   **Formalization Note** Only display (4) is formalized. The printed theorem continues "and for any δ > 0 with probability at least 1 − δ," and gives no conclusion for that clause, so it is not stated.
-- source:
--   arXiv:1306.0940v5, Theorem 2, (4), p. 5

import Mathlib
import Definitions.Def_PosteriorSamplingRL_Regret_Run

open MeasureTheory ProbabilityTheory

namespace PosteriorSamplingRL.Regret

/-- Theorem 2 (Regret equivalence), (4) (arXiv:1306.0940v5, p. 5):
`E[∑_{k=1}^m Δ_k] = E[∑_{k=1}^m Δ̃_k]` for every number of episodes `m`. -/
theorem theorem2_regret_equivalence (S A τ : ℕ) (hS : 1 ≤ S) (hA : 1 ≤ A) (hτ : 1 ≤ τ)
    (Θ : Type) [MeasurableSpace Θ] (F : MDPFamily S A Θ) (ρ : Fin S → ℝ) (hρ : IsDist ρ)
    (f : Measure Θ) (sel : Θ → Policy S A τ) (hsel : ∀ θ, IsOptimal F θ (sel θ))
    (hsel_meas : Measurable sel)
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R : PSRLRun F ρ f sel μ) (m : ℕ) :
    ∫ ω, ∑ k ∈ Finset.range m, R.Δ k ω ∂μ = ∫ ω, ∑ k ∈ Finset.range m, R.Δtilde k ω ∂μ := by sorry

end PosteriorSamplingRL.Regret
