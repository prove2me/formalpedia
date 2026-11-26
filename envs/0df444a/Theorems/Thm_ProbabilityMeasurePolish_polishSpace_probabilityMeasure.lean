-- Prove2me | Theorems.Thm_ProbabilityMeasurePolish_polishSpace_probabilityMeasure
-- name    : ProbabilityMeasurePolish.polishSpace_probabilityMeasure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:16:02.552803+00:00
-- url     : https://prove2.me/theorems/6a0b5490-1231-470c-8498-1c705f443cb5
-- title:
--   Probability Measure Polish: polish Space probability Measure
-- statement:
--   **The space of probability measures on a Polish space is Polish** (Parthasarathy,
--   *Probability Measures on Metric Spaces*, Chapter II §6, "The Weak Topology in the Space of
--   Measures").
--
--   Let `X` be a Polish space carrying its Borel σ-algebra.  Then `ProbabilityMeasure X`, the
--   space of Borel probability measures on `X` with the topology of weak convergence, is again
--   Polish: the topology is second countable and admits a complete compatible metric.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/SolutionPolish.lean#L70-L73
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/SolutionPolish.lean#L70-L73

import Mathlib
import Definitions.Def_BicausalOT_DescriptiveSetTheory_ProbabilityMeasurePolish
import Definitions.Def_SolutionPolish
set_option autoImplicit false
open MeasureTheory
open ProbabilityMeasurePolish

theorem ProbabilityMeasurePolish.polishSpace_probabilityMeasure {X : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] :
    PolishSpace (ProbabilityMeasure X) := by sorry
