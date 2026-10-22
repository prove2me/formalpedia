-- Prove2me | Theorems.Thm_SeqSocialLearning_Adequate_sufficiency
-- name    : SeqSocialLearning.Adequate.sufficiency
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-21T09:39:54.871246+00:00
-- url     : https://prove2.me/theorems/f4a11c1e-dc12-4474-90fa-2d281c50cf69
-- title:
--   Theorem 1, p. 5 — sufficiency: totally unbounded signals imply adequate learning
-- statement:
--   Let $(\Omega,\mu,A,S,F)$ be a social learning model:
--
--   1. $\Omega$ is a separable complete metric state space with prior $\mu$;
--   2. $A$ is a compact metric action space with at least two actions;
--   3. $S$ is a standard Borel signal space;
--   4. $F$ is a Markov kernel whose signal distributions are mutually absolutely continuous and distinct across states.
--
--   If $(F,\mu)$ features **totally unbounded signals**, then **adequate learning** holds:
--   $$\mathrm{TotallyUnbounded}(F,\mu)\ \Longrightarrow\ \forall u\in U:\ \mathrm{AsymptoticLearning}(u).$$
--   Here asymptotic learning for $u$ means that in every perfect Bayesian equilibrium $\sigma$ the realized payoff $u(a_t,\omega)$ converges $P_\sigma$-almost surely to $O(\omega)=\max_a u(a,\omega)$.
--
--   This is the sufficiency ("if") direction of Theorem 1. The paper proves it with the vanishing value of private information (Lemma 1), the degenerate belief at infinity (Lemma 2), and Lemmas 3–8. The converse direction is the milestone `SeqSocialLearning.Adequate.necessity`. Together the two directions give `SeqSocialLearning.Adequate.theorem_1`.
-- source:
--   Arieli & Mueller-Frank, A General Analysis of Sequential Social Learning, SSRN 2466903 (version of February 21, 2019), p. 5, Theorem 1 (sufficiency direction); published in Mathematics of Operations Research 46(4):1235-1249 (2021)

import Mathlib
import Definitions.Def_SeqSocialLearning_Adequate_Model
import Definitions.Def_SeqSocialLearning_Adequate_Signals

open MeasureTheory ProbabilityTheory

namespace SeqSocialLearning.Adequate

/-- **Sufficiency in Theorem 1** (p. 5). If `(F, µ)` features totally unbounded signals, then
adequate learning holds: asymptotic learning holds for every utility `u ∈ U`. -/
theorem sufficiency {Ω A S : Type*}
    [MetricSpace Ω] [CompleteSpace Ω] [TopologicalSpace.SeparableSpace Ω]
    [MeasurableSpace Ω] [BorelSpace Ω] [Nonempty Ω]
    [MetricSpace A] [CompactSpace A] [MeasurableSpace A] [BorelSpace A] [Nontrivial A]
    [MeasurableSpace S] [StandardBorelSpace S]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Kernel Ω S) [IsMarkovKernel F]
    (hF : Standing F) :
    TotallyUnbounded μ F → AdequateLearning (A := A) μ F := by sorry

end SeqSocialLearning.Adequate
