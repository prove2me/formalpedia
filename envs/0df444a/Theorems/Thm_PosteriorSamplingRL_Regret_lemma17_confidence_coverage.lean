-- Prove2me | Theorems.Thm_PosteriorSamplingRL_Regret_lemma17_confidence_coverage
-- name    : PosteriorSamplingRL.Regret.lemma17_confidence_coverage
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T21:06:08.257034+00:00
-- url     : https://prove2.me/theorems/cb29741a-b293-4dc6-893e-35b7f2649b7c
-- title:
--   §5.2, p. 7 (Lemma 17 of [4]) — P(M* ∉ 𝓜_k) ≤ 1/m for the widths β_k(s,a)
-- statement:
--   Consider a PSRL run with $M^*\sim f$ and the confidence sets $\mathcal M_k$ with widths $\beta_k(s,a)=\sqrt{14S\log(2SAm\,t_k)/\max\{1,N_{t_k}(s,a)\}}$ built for $m$ episodes. For each of the first $m$ episodes $k$,
--   $$
--   \mathbb P\big(M^*\notin\mathcal M_k\big)\le\frac1m .
--   $$
--
--   The paper takes this from Lemma 17 of Jaksch, Ortner and Auer (2010), whose confidence sets coincide with $\mathcal M_k$ when their parameter is $\delta=1/m$. Together with Lemma 1 it bounds the expected number of episodes in which either $M^*$ or $M_k$ leaves its confidence set.
--
--   **Formalization Note** The paper gives no proof; the statement is posed here for this model, in which rewards are drawn from distributions on $[0,1]$, the state is reset from $\rho$ at every episode start and every transition, including the last of each episode, is observed. In Lean's 0-based episodes the condition is $k<m$ and $t_k=k\tau+1$.
-- source:
--   arXiv:1306.0940v5, §5.2, p. 7 (citing Lemma 17 of Jaksch, Ortner & Auer 2010, and footnote 3)

import Mathlib
import Definitions.Def_PosteriorSamplingRL_Regret_Confidence

open MeasureTheory ProbabilityTheory

namespace PosteriorSamplingRL.Regret

/-- §5.2 (arXiv:1306.0940v5, p. 7), citing Lemma 17 of Jaksch, Ortner & Auer (2010) with
`δ = 1/m`: for each of the first `m` episodes `k`, `P(M* ∉ 𝓜_k) ≤ 1/m`. -/
theorem lemma17_confidence_coverage (S A τ : ℕ) (hS : 1 ≤ S) (hA : 1 ≤ A) (hτ : 1 ≤ τ)
    (Θ : Type) [MeasurableSpace Θ] (F : MDPFamily S A Θ) (ρ : Fin S → ℝ) (hρ : IsDist ρ)
    (f : Measure Θ) (sel : Θ → Policy S A τ) (hsel : ∀ θ, IsOptimal F θ (sel θ))
    (hsel_meas : Measurable sel)
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R : PSRLRun F ρ f sel μ) (m k : ℕ) (hk : k < m) :
    μ.real {ω | ¬ R.InConf m k (R.Mstar ω) ω} ≤ 1 / (m : ℝ) := by sorry

end PosteriorSamplingRL.Regret
