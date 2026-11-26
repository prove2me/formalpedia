-- Prove2me | Theorems.Thm_WeakP_measurable_toMeasure
-- name    : WeakP.measurable_toMeasure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:12:02.970912+00:00
-- url     : https://prove2.me/theorems/6f56703a-99c2-4cdb-a1e9-172fee382ff7
-- title:
--   Weak P: measurable to Measure
-- statement:
--   **W2, packaged**: the underlying-measure map is measurable from the
--       Borel σ-algebra of the weak topology to the Giry σ-algebra.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/SemianalyticValue.lean#L60-L63
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/SemianalyticValue.lean#L60-L63

import Definitions.Def_BicausalOT_MultiPeriodTopology
import Definitions.Def_BicausalOT_FeasNonempty
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LsaAlgebra
import Definitions.Def_BicausalOT_DescriptiveSetTheory_KernelIntegral
import Definitions.Def_BicausalOT_DescriptiveSetTheory_ProbabilityMeasurePolish
import Definitions.Def_BicausalOT_SemianalyticValue
set_option autoImplicit false
open MeasureTheory Set ENNReal
noncomputable section
open WeakP
variable {W : Type*} [MeasurableSpace W] [TopologicalSpace W]
  [OpensMeasurableSpace W]

theorem WeakP.measurable_toMeasure [PolishSpace W] [BorelSpace W] :
    Measurable (toMeasure : WeakP W → Measure W) := by sorry
