-- Prove2me | Theorems.Thm_SeqSocialLearning_Adequate_necessity
-- name    : SeqSocialLearning.Adequate.necessity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:14:14.289027+00:00
-- url     : https://prove2.me/theorems/9f4933c9-64f1-4dfe-857b-719700f40307
-- title:
--   Theorem 1, necessity (§3, pp. 5, 7) — without totally unbounded signals some u ∈ U has no asymptotic learning
-- statement:
--   Let $(\Omega,\mu,A,S,F)$ be a social learning model. If the information structure $(F,\mu)$ does not feature totally unbounded signals, then there exists a utility function $u \in U$ for which asymptotic learning fails:
--   $$
--   \neg\,\mathrm{TotallyUnbounded}(F,\mu) \implies \exists\, u \in U:\ \neg\,\mathrm{AsymptoticLearning}(u).
--   $$
--
--   This is the necessary direction of Theorem 1, proved on p. 7.
-- source:
--   Arieli & Mueller-Frank, A General Analysis of Sequential Social Learning, SSRN 2466903 (version of February 21, 2019), p. 5 (statement), p. 7, §3 Proof of Necessity

import Mathlib
import Definitions.Def_SeqSocialLearning_Adequate_Model
import Definitions.Def_SeqSocialLearning_Adequate_Signals

open MeasureTheory ProbabilityTheory Filter Topology

namespace SeqSocialLearning.Adequate

/-- **Necessity in Theorem 1** (§3, stated p. 5, proved p. 7). If signals fail to be totally
unbounded, then there exists a utility function `u ∈ U` for which asymptotic learning fails. -/
theorem necessity {Ω A S : Type*}
    [MetricSpace Ω] [CompleteSpace Ω] [TopologicalSpace.SeparableSpace Ω]
    [MeasurableSpace Ω] [BorelSpace Ω] [Nonempty Ω]
    [MetricSpace A] [CompactSpace A] [MeasurableSpace A] [BorelSpace A] [Nontrivial A]
    [MeasurableSpace S] [StandardBorelSpace S]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Kernel Ω S) [IsMarkovKernel F]
    (hF : Standing F) :
    ¬ TotallyUnbounded μ F → ∃ u : A → Ω → ℝ, InU u ∧ ¬ AsymptoticLearning μ F u := by sorry

end SeqSocialLearning.Adequate
