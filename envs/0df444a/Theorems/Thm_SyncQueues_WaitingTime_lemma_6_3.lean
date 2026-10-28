-- Prove2me | Theorems.Thm_SyncQueues_WaitingTime_lemma_6_3
-- name    : SyncQueues.WaitingTime.lemma_6_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T05:12:54.506358+00:00
-- url     : https://prove2.me/theorems/c4bbef6f-fe6e-448b-9fe3-fd35fca8b62c
-- title:
--   Lemma 6.3, p. 27 — ‖X₁∨X₂ − Y₁∨Y₂‖_p ≤ ‖X₂‖_p + ‖Y₂‖_p + ‖X₁ − Y₁‖_p for nonnegative random variables
-- statement:
--   Let $X_1,X_2,Y_1,Y_2$ be nonnegative random variables on a probability space and let $p\ge1$. Then
--   $$\Big(E\big[|X_1\vee X_2-Y_1\vee Y_2|^p\big]\Big)^{1/p}\le\big(E[X_2^p]\big)^{1/p}+\big(E[Y_2^p]\big)^{1/p}+\Big(E\big[|X_1-Y_1|^p\big]\Big)^{1/p}.$$
--
--   It is the elementary inequality that splits the predecessor graph into its tree part and its merged part in the proof of Proposition 6.4.
--
--   **Formalization Note** The $L^p$ norms are `eLpNorm` with values in $[0,\infty]$, so the inequality is stated also when some moment is infinite. Random variables are almost everywhere strongly measurable real functions, nonnegative everywhere.
-- source:
--   Olvera-Cravioto & Ruiz-Lacedelli, arXiv:1501.00186v3, p. 27, Lemma 6.3

import Mathlib

namespace SyncQueues.WaitingTime

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

theorem lemma_6_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₁ X₂ Y₁ Y₂ : Ω → ℝ)
    (hX₁ : AEStronglyMeasurable X₁ P) (hX₂ : AEStronglyMeasurable X₂ P)
    (hY₁ : AEStronglyMeasurable Y₁ P) (hY₂ : AEStronglyMeasurable Y₂ P)
    (hX₁0 : ∀ ω, 0 ≤ X₁ ω) (hX₂0 : ∀ ω, 0 ≤ X₂ ω) (hY₁0 : ∀ ω, 0 ≤ Y₁ ω) (hY₂0 : ∀ ω, 0 ≤ Y₂ ω)
    {p : ℝ} (hp : 1 ≤ p) :
    eLpNorm (fun ω => max (X₁ ω) (X₂ ω) - max (Y₁ ω) (Y₂ ω)) (ENNReal.ofReal p) P ≤
      eLpNorm X₂ (ENNReal.ofReal p) P + eLpNorm Y₂ (ENNReal.ofReal p) P +
        eLpNorm (fun ω => X₁ ω - Y₁ ω) (ENNReal.ofReal p) P := by sorry

end SyncQueues.WaitingTime
