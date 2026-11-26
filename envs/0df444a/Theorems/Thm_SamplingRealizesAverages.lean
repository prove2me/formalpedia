-- Prove2me | Theorems.Thm_SamplingRealizesAverages
-- name    : SamplingRealizesAverages
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:47:57.186242+00:00
-- url     : https://prove2.me/theorems/6735e6ef-41d5-4651-8d51-d5945d19b366
-- title:
--   Sampling Realizes Averages: Sampling Realizes Averages
-- statement:
--   The abstract content of the Strong Law delegation cited at paper.tex line 1295
--   ([GHS, Theorem 2.1]): one sample sequence `x : ℕ → X` realizing countably many strong-law
--   averages at once, while staying entirely inside a prescribed `mu`-full-measure set `S`.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/SamplingRealizesAverages.lean#L9-L64
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/SamplingRealizesAverages.lean#L9-L64

import Definitions.Def_Tablet_Preamble
import Definitions.Def_Tablet_SamplingRealizesAverages
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Finset Function

theorem SamplingRealizesAverages
    {X : Type*} [MeasurableSpace X] (mu : Measure X) [IsProbabilityMeasure mu]
    (g : ℕ → X → ℝ) (hgm : ∀ j, Measurable (g j)) (hg : ∀ j, Integrable (g j) mu)
    (S : Set X) (hSm : MeasurableSet S) (hS : mu Sᶜ = 0) :
    ∃ x : ℕ → X, (∀ i, x i ∈ S) ∧
      ∀ j, Tendsto (fun n : ℕ => (∑ i ∈ range n, g j (x i)) / n) atTop
        (nhds (∫ y, g j y ∂mu)) := by sorry
