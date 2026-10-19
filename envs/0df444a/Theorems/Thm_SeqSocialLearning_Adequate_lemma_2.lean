-- Prove2me | Theorems.Thm_SeqSocialLearning_Adequate_lemma_2
-- name    : SeqSocialLearning.Adequate.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:15:05.416227+00:00
-- url     : https://prove2.me/theorems/012c051b-1f77-4636-9d56-f0403222bbff
-- title:
--   Lemma 2, p. 11 — in every PBE the limit public belief µ_∞(·|h) is a degenerate prior for Pσ-a.e. history
-- statement:
--   Let $\sigma$ be a perfect Bayesian equilibrium of the game defined by $(F, \mu, u, A)$ with $u \in U$. Let $\mu_\infty(\cdot\mid h)$ be the public belief about the state given the infinite history $h$ of actions, and let $D$ be the set of degenerate priors: those $\nu$ for which the first agent's value of private information in the game $(\Omega,\nu,F,u)$ is zero. Then
--   $$
--   \mu_\infty(\cdot\mid h) \in D \qquad \text{for } P_\sigma\text{-almost every history } h .
--   $$
--
--   In the limit, one more private signal is worthless to an agent who holds the public belief. The proof of Theorem 1 contradicts this lemma.
--
--   **Formalization Note** A prior $\nu$ is degenerate when $\int_S \max_a E_{\nu F(\cdot\mid s)}[u(a,\omega)]\,d(\nu F)(s) = \max_a E_\nu[u(a,\omega)]$. This is the first agent's equilibrium value with its signal set equal to its value without it.
-- source:
--   Arieli & Mueller-Frank, A General Analysis of Sequential Social Learning, SSRN 2466903 (version of February 21, 2019), p. 11, Lemma 2 (D defined p. 10)

import Mathlib
import Definitions.Def_SeqSocialLearning_Adequate_Model
import Definitions.Def_SeqSocialLearning_Adequate_Signals
import Definitions.Def_SeqSocialLearning_Adequate_Beliefs

open MeasureTheory ProbabilityTheory Filter Topology

namespace SeqSocialLearning.Adequate

/-- **Lemma 2** (p. 11). Let `σ` be a perfect Bayesian equilibrium of the game defined by
`(F, µ, u, A)`. Then the belief at infinity `µ_∞(· | h)` is a degenerate prior for `Pσ`-almost
every infinite history `h`. -/
theorem lemma_2 {Ω A S : Type*}
    [MetricSpace Ω] [CompleteSpace Ω] [TopologicalSpace.SeparableSpace Ω]
    [MeasurableSpace Ω] [BorelSpace Ω] [Nonempty Ω]
    [MetricSpace A] [CompactSpace A] [MeasurableSpace A] [BorelSpace A] [Nontrivial A]
    [MeasurableSpace S] [StandardBorelSpace S]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Kernel Ω S) [IsMarkovKernel F]
    (hF : Standing F)
    (u : A → Ω → ℝ) (hu : InU u) (p : Profile A S) (hp : IsPBE μ F u p) :
    ∀ᵐ x ∂(playMeasure μ F p),
      IsDegenerate (limitBelief μ F p (fullHistory x)) F u := by sorry

end SeqSocialLearning.Adequate
