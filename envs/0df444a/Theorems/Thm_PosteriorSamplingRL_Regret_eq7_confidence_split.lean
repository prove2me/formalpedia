-- Prove2me | Theorems.Thm_PosteriorSamplingRL_Regret_eq7_confidence_split
-- name    : PosteriorSamplingRL.Regret.eq7_confidence_split
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T21:06:18.220519+00:00
-- url     : https://prove2.me/theorems/d93f10fc-af46-43bf-8515-ac5798f1f880
-- title:
--   (7), §5.2, p. 6 — Σ Δ̃_k ≤ Σ Δ̃_k 1{M_k, M* ∈ 𝓜_k} + τ Σ [1{M_k ∉ 𝓜_k} + 1{M* ∉ 𝓜_k}]
-- statement:
--   Consider a PSRL run and the confidence sets $\mathcal M_k$ built for $m$ episodes. On every sample path,
--   $$
--   \sum_{k=1}^m\tilde\Delta_k\le\sum_{k=1}^m\tilde\Delta_k\,\mathbf 1\{M_k,M^*\in\mathcal M_k\}+\tau\sum_{k=1}^m\big[\mathbf 1\{M_k\notin\mathcal M_k\}+\mathbf 1\{M^*\notin\mathcal M_k\}\big].
--   $$
--
--   The inequality follows from $\tilde\Delta_k\le\tau$, which holds because rewards lie in $[0,1]$ and values are sums of at most $\tau$ mean rewards. It splits the regret into a part on the confidence event and a part controlled by the probability of leaving it.
--
--   **Formalization Note** The statement is pathwise (for every $\omega$). The page's "using that $\tilde\Delta_k\le\tau$" is a consequence of the model (reward support $[0,1]$, $\rho$ a distribution), not a hypothesis.
-- source:
--   arXiv:1306.0940v5, §5.2, (7), p. 6

import Mathlib
import Definitions.Def_PosteriorSamplingRL_Regret_Confidence

open MeasureTheory ProbabilityTheory

namespace PosteriorSamplingRL.Regret

open Classical in
/-- (7), §5.2 (arXiv:1306.0940v5, p. 6), pathwise: using `Δ̃_k ≤ τ`,
`∑_{k=1}^m Δ̃_k ≤ ∑_{k=1}^m Δ̃_k 1{M_k, M* ∈ 𝓜_k} + τ ∑_{k=1}^m [1{M_k ∉ 𝓜_k} + 1{M* ∉ 𝓜_k}]`. -/
theorem eq7_confidence_split (S A τ : ℕ) (hS : 1 ≤ S) (hA : 1 ≤ A) (hτ : 1 ≤ τ)
    (Θ : Type) [MeasurableSpace Θ] (F : MDPFamily S A Θ) (ρ : Fin S → ℝ) (hρ : IsDist ρ)
    (f : Measure Θ) (sel : Θ → Policy S A τ) (hsel : ∀ θ, IsOptimal F θ (sel θ))
    (hsel_meas : Measurable sel)
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R : PSRLRun F ρ f sel μ) (m : ℕ) (ω : Ω) :
    ∑ k ∈ Finset.range m, R.Δtilde k ω
      ≤ ∑ k ∈ Finset.range m, R.Δtilde k ω *
            (if R.InConf m k (R.Msamp k ω) ω ∧ R.InConf m k (R.Mstar ω) ω then 1 else 0)
        + τ * ∑ k ∈ Finset.range m,
            ((if R.InConf m k (R.Msamp k ω) ω then 0 else 1)
              + (if R.InConf m k (R.Mstar ω) ω then 0 else 1)) := by sorry

end PosteriorSamplingRL.Regret
