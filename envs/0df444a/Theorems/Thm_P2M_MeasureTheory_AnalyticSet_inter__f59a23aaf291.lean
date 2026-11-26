-- Prove2me | Theorems.Thm_P2M_MeasureTheory_AnalyticSet_inter__f59a23aaf291
-- name    : P2M_MeasureTheory_AnalyticSet_inter__f59a23aaf291
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:03:13.428505+00:00
-- url     : https://prove2.me/theorems/4884e9d1-db96-4b25-ab97-e492c8041732
-- title:
--   P2 M Measure Theory Analytic Set inter  f59a23aaf291: P2 M Measure Theory Analytic Set inter  f59a23aaf291
-- statement:
--   The P2 M Measure Theory Analytic Set inter  f59a23aaf291 construction uses the P2 M Measure Theory Analytic Set inter  f59a23aaf291 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/KernelIntegral.lean#L32-L39
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/KernelIntegral.lean#L32-L39

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

theorem P2M_MeasureTheory_AnalyticSet_inter__f59a23aaf291
    {W : Type*} [TopologicalSpace W] [T2Space W]
    {S T : Set W} (hS : AnalyticSet S) (hT : AnalyticSet T) :
    AnalyticSet (S ∩ T) := by sorry

alias «MeasureTheory».«AnalyticSet».«inter'» := P2M_MeasureTheory_AnalyticSet_inter__f59a23aaf291
