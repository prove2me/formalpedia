-- Prove2me | Theorems.Thm_SeqSocialLearning_Adequate_lemma_5
-- name    : SeqSocialLearning.Adequate.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:14:23.118744+00:00
-- url     : https://prove2.me/theorems/f994bdbb-9498-48d0-a383-2288a437fdbd
-- title:
--   Lemma 5 (first part), p. 15 — total unboundedness passes to any prior ν ≪ µ with dν/dµ ≤ C
-- statement:
--   Let $(F,\mu)$ feature totally unbounded signals. Let $\nu \in \Delta(\Omega)$ be absolutely continuous with respect to $\mu$, with
--   $$
--   \frac{d\nu}{d\mu}(\omega) \le C \quad \text{for } \mu\text{-almost every } \omega,
--   $$
--   for some $C > 0$. Then $(F,\nu)$ features totally unbounded signals.
--
--   In the proof of Theorem 1, this lemma and Lemma 7 carry total unboundedness from the prior $\mu$ to an averaged limit belief.
--
--   **Formalization Note** Only the first sentence pair of Lemma 5 is stated. The second part (pairwise unbounded signals, signals unbounded with respect to $u$) concerns Theorems 2 and 3 and is not part of this mission.
-- source:
--   Arieli & Mueller-Frank, A General Analysis of Sequential Social Learning, SSRN 2466903 (version of February 21, 2019), p. 15, Lemma 5 (first part)

import Mathlib
import Definitions.Def_SeqSocialLearning_Adequate_Model
import Definitions.Def_SeqSocialLearning_Adequate_Signals

open MeasureTheory ProbabilityTheory Filter Topology

namespace SeqSocialLearning.Adequate

/-- **Lemma 5**, first part (p. 15). If `(F, µ)` features totally unbounded signals and
`ν ∈ ∆(Ω)` is absolutely continuous with respect to `µ` with `dν/dµ ≤ C` `µ`-a.e. for some
`C > 0`, then `(F, ν)` features totally unbounded signals. -/
theorem lemma_5 {Ω A S : Type*}
    [MetricSpace Ω] [CompleteSpace Ω] [TopologicalSpace.SeparableSpace Ω]
    [MeasurableSpace Ω] [BorelSpace Ω] [Nonempty Ω]
    [MetricSpace A] [CompactSpace A] [MeasurableSpace A] [BorelSpace A] [Nontrivial A]
    [MeasurableSpace S] [StandardBorelSpace S]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Kernel Ω S) [IsMarkovKernel F]
    (hF : Standing F)
    (hTU : TotallyUnbounded μ F)
    (ν : Measure Ω) [IsProbabilityMeasure ν] (hνμ : ν ≪ μ) (C : ℝ) (hC : 0 < C)
    (hbound : ∀ᵐ ω ∂μ, ν.rnDeriv μ ω ≤ ENNReal.ofReal C) :
    TotallyUnbounded ν F := by sorry

end SeqSocialLearning.Adequate
