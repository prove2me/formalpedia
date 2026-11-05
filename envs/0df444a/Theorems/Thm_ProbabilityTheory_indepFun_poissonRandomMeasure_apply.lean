-- Prove2me | Theorems.Thm_ProbabilityTheory_indepFun_poissonRandomMeasure_apply
-- name    : ProbabilityTheory.indepFun_poissonRandomMeasure_apply
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T06:49:26.320582+00:00
-- url     : https://prove2.me/theorems/85778888-daa3-4c7f-91ab-ba65accaa135
-- title:
--   LeanLevy: ProbabilityTheory.indepFun_poissonRandomMeasure_apply
-- statement:
--   Source-header theorem from the pinned LeanLevy library. The source section variables are declared in the preamble. Its original proof has not been transplanted or verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/PoissonRandomMeasure.lean#L735

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
open MeasureTheory Complex ComplexConjugate Set Filter Topology Finset ProbabilityTheory
open scoped NNReal ENNReal
variable {Ω E : Type} [MeasurableSpace E] [MeasurableSpace Ω] {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E} {m : Measure E} [SigmaFinite m] [Nonempty E] {μ : Measure Ω} {A B : Set E} {ω : Ω}

theorem ProbabilityTheory.indepFun_poissonRandomMeasure_apply [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hfinA : m A < ⊤) (hfinB : m B < ⊤) (hAB : Disjoint A B) :
    IndepFun (fun ω => poissonRandomMeasure K X ω A) (fun ω => poissonRandomMeasure K X ω B) μ := by sorry
