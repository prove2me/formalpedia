-- Prove2me | Theorems.Thm_SeqSocialLearning_Adequate_theorem_1
-- name    : SeqSocialLearning.Adequate.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:14:11.48634+00:00
-- url     : https://prove2.me/theorems/eb5c4dea-4c12-4091-a7f0-07df90d9e5f0
-- title:
--   Theorem 1, p. 5 — adequate learning holds if and only if signals are totally unbounded
-- statement:
--   Let $(\Omega,\mu,A,S,F)$ be a social learning model:
--
--   1. $\Omega$ is a separable complete metric state space with prior $\mu$;
--   2. $A$ is a compact metric action space with at least two actions;
--   3. $S$ is a standard Borel signal space;
--   4. $F$ is a Markov kernel whose signal distributions are mutually absolutely continuous and distinct across states.
--
--   Then
--   $$
--   \text{adequate learning holds} \iff (F,\mu) \text{ features totally unbounded signals}.
--   $$
--   Adequate learning means: for every bounded measurable utility $u$ that is continuous in actions, and every perfect Bayesian equilibrium, the realized payoffs converge almost surely to the maximal payoff $O(\omega) = \max_a u(a,\omega)$. Totally unbounded signals means: for every event with prior probability strictly between $0$ and $1$, the support of the posterior of that event given one private signal contains both $0$ and $1$.
--
--   This is the paper's main result. It extends Smith and Sorensen's binary characterization to general state and action spaces.
--
--   **Formalization Note** The state space carries the hypothesis `Nonempty Ω`, which already follows from $\mu$ being a probability measure. Equilibria are perfect Bayesian in the ex-ante sense of p. 4, over mixed strategies. Agents are indexed from $0$.
-- source:
--   Arieli & Mueller-Frank, A General Analysis of Sequential Social Learning, SSRN 2466903 (version of February 21, 2019), p. 5, Theorem 1

import Mathlib
import Definitions.Def_SeqSocialLearning_Adequate_Model
import Definitions.Def_SeqSocialLearning_Adequate_Signals

open MeasureTheory ProbabilityTheory

namespace SeqSocialLearning.Adequate

/-- **Theorem 1** (p. 5). In a social learning model `(Ω, µ, A, S, F)`, adequate learning holds
if and only if signals are totally unbounded. -/
theorem theorem_1 {Ω A S : Type*}
    [MetricSpace Ω] [CompleteSpace Ω] [TopologicalSpace.SeparableSpace Ω]
    [MeasurableSpace Ω] [BorelSpace Ω] [Nonempty Ω]
    [MetricSpace A] [CompactSpace A] [MeasurableSpace A] [BorelSpace A] [Nontrivial A]
    [MeasurableSpace S] [StandardBorelSpace S]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Kernel Ω S) [IsMarkovKernel F]
    (hF : Standing F) :
    AdequateLearning (A := A) μ F ↔ TotallyUnbounded μ F := by sorry

end SeqSocialLearning.Adequate
