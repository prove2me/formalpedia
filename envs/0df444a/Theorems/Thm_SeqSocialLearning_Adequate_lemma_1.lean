-- Prove2me | Theorems.Thm_SeqSocialLearning_Adequate_lemma_1
-- name    : SeqSocialLearning.Adequate.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:15:03.347402+00:00
-- url     : https://prove2.me/theorems/ffa24014-5ed3-4ed3-8ffc-90aab84bb6d3
-- title:
--   Lemma 1, p. 6 — vanishing value of private information: d_t → 0 almost surely in every PBE
-- statement:
--   Consider a sequential social learning game $(\Omega,\mu,A,S,F)$ with a utility $u \in U$, and let $\sigma$ be a perfect Bayesian equilibrium with play measure $P_\sigma$. Let $d_t = E_\sigma[y_t - \hat y_t \mid h_t]$ be agent $t$'s value of private information: the expected gain from its private signal over the best action against the public history alone. Then
--   $$
--   d_t \xrightarrow[t\to\infty]{} 0 \qquad P_\sigma\text{-almost surely}.
--   $$
--
--   This is the principle of the vanishing value of private information. The sufficiency direction of Theorem 1 rests on it, through Lemma 2.
--
--   **Formalization Note** Agents are indexed from $0$ (Lean's agent $t$ is the paper's agent $t+1$). $d_t$ is $E_\sigma[y_t\mid\mathcal H_t]-\hat y_t$, with $\hat y_t$ computed from the public belief, a regular conditional distribution.
-- source:
--   Arieli & Mueller-Frank, A General Analysis of Sequential Social Learning, SSRN 2466903 (version of February 21, 2019), p. 6, Lemma 1 (notation p. 5)

import Mathlib
import Definitions.Def_SeqSocialLearning_Adequate_Model
import Definitions.Def_SeqSocialLearning_Adequate_Signals
import Definitions.Def_SeqSocialLearning_Adequate_Beliefs

open MeasureTheory ProbabilityTheory Filter Topology

namespace SeqSocialLearning.Adequate

/-- **Lemma 1** (p. 6), the principle of the vanishing value of private information: in every
perfect Bayesian equilibrium `σ` the value of private information `d_t` converges to zero
`Pσ`-almost surely. -/
theorem lemma_1 {Ω A S : Type*}
    [MetricSpace Ω] [CompleteSpace Ω] [TopologicalSpace.SeparableSpace Ω]
    [MeasurableSpace Ω] [BorelSpace Ω] [Nonempty Ω]
    [MetricSpace A] [CompactSpace A] [MeasurableSpace A] [BorelSpace A] [Nontrivial A]
    [MeasurableSpace S] [StandardBorelSpace S]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Kernel Ω S) [IsMarkovKernel F]
    (hF : Standing F)
    (u : A → Ω → ℝ) (hu : InU u) (p : Profile A S) (hp : IsPBE μ F u p) :
    ∀ᵐ x ∂(playMeasure μ F p),
      Tendsto (fun t => valuePrivInfo μ F p u t x) atTop (𝓝 0) := by sorry

end SeqSocialLearning.Adequate
