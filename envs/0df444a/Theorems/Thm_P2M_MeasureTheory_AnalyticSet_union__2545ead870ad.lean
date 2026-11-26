-- Prove2me | Theorems.Thm_P2M_MeasureTheory_AnalyticSet_union__2545ead870ad
-- name    : P2M_MeasureTheory_AnalyticSet_union__2545ead870ad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:03:15.429685+00:00
-- url     : https://prove2.me/theorems/20df143c-f9ff-4c61-af83-5bed5580e359
-- title:
--   P2 M Measure Theory Analytic Set union  2545ead870ad: P2 M Measure Theory Analytic Set union  2545ead870ad
-- statement:
--   The P2 M Measure Theory Analytic Set union  2545ead870ad construction uses the P2 M Measure Theory Analytic Set union  2545ead870ad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/KernelIntegral.lean#L41-L48
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/KernelIntegral.lean#L41-L48

import Definitions.Def_BicausalOT_DescriptiveSetTheory_Capacitability
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LowerSemianalytic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
import Definitions.Def_BicausalOT_DescriptiveSetTheory_KernelIntegral
set_option autoImplicit false
open Set Topology MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal
noncomputable section

theorem P2M_MeasureTheory_AnalyticSet_union__2545ead870ad
    {W : Type*} [TopologicalSpace W]
    {S T : Set W} (hS : AnalyticSet S) (hT : AnalyticSet T) :
    AnalyticSet (S ∪ T) := by sorry

alias «MeasureTheory».«AnalyticSet».«union'» := P2M_MeasureTheory_AnalyticSet_union__2545ead870ad
