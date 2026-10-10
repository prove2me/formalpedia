-- Prove2me | Theorems.Thm_PosteriorSamplingRL_Regret_lemma1_posterior_sampling
-- name    : PosteriorSamplingRL.Regret.lemma1_posterior_sampling
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T21:02:48.389988+00:00
-- url     : https://prove2.me/theorems/43e98ac6-6f6a-42d1-8ad9-e848b35c3d3e
-- title:
--   Lemma 1, p. 5 — posterior sampling: E[g(M*, H_{t_k}) | H_{t_k}] = E[g(M_k, H_{t_k}) | H_{t_k}]
-- statement:
--   Consider a PSRL run in which the true MDP $M^*$ has the prior distribution $f$, and let $H_{t_k}$ be the history available at the start of episode $k$. For every bounded measurable function $g(M,H_{t_k})$ of an MDP and the history,
--   $$
--   \mathbb E\big[g(M^*,H_{t_k})\,\big|\,H_{t_k}\big]=\mathbb E\big[g(M_k,H_{t_k})\,\big|\,H_{t_k}\big]\qquad\text{almost surely.}
--   $$
--
--   This is the observation on which the whole analysis rests: given the history, the true MDP and the sampled MDP are identically distributed. Taking expectations gives $\mathbb E[g(M^*)]=\mathbb E[g(M_k)]$.
--
--   **Formalization Note** The paper's "$\sigma(H_{t_k})$-measurable function $g$" is read as a function of $(M,H_{t_k})$, as the proof of (8) applies the lemma to $g=\mathbf 1\{M\notin\mathcal M_k\}$, where $\mathcal M_k$ depends on $H_{t_k}$. Boundedness of $g$ is added; the page states no integrability condition, and every use of the lemma (indicators, value differences bounded by $\tau$) is bounded. The standing hypotheses $S,A,\tau\ge1$, $\rho$ a distribution and the optimality of the selector are carried for uniformity with the other statements.
-- source:
--   arXiv:1306.0940v5, Lemma 1, (2), p. 5

import Mathlib
import Definitions.Def_PosteriorSamplingRL_Regret_Run

open MeasureTheory ProbabilityTheory

namespace PosteriorSamplingRL.Regret

/-- Lemma 1 (Posterior Sampling; arXiv:1306.0940v5, p. 5). If `f` is the distribution of `M*`,
then for every episode `k` and every bounded measurable `g(M, H_{t_k})`,
`E[g(M*, H_{t_k}) | H_{t_k}] = E[g(M_k, H_{t_k}) | H_{t_k}]` almost surely. -/
theorem lemma1_posterior_sampling (S A τ : ℕ) (hS : 1 ≤ S) (hA : 1 ≤ A) (hτ : 1 ≤ τ)
    (Θ : Type) [MeasurableSpace Θ] (F : MDPFamily S A Θ) (ρ : Fin S → ℝ) (hρ : IsDist ρ)
    (f : Measure Θ) (sel : Θ → Policy S A τ) (hsel : ∀ θ, IsOptimal F θ (sel θ))
    (hsel_meas : Measurable sel)
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R : PSRLRun F ρ f sel μ) (k : ℕ) (g : Θ × Hist S A τ k → ℝ) (hg : Measurable g)
    (hg_bdd : ∃ C : ℝ, ∀ x, |g x| ≤ C) :
    μ[fun ω => g (R.Mstar ω, R.hist k ω) | R.histSigma k]
      =ᵐ[μ] μ[fun ω => g (R.Msamp k ω, R.hist k ω) | R.histSigma k] := by sorry

end PosteriorSamplingRL.Regret
