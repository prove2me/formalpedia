-- Prove2me | Theorems.Thm_P2M_MultiPeriod_couplingSet__weakP_nonempty_46c7c592b32c
-- name    : P2M_MultiPeriod_couplingSet__weakP_nonempty_46c7c592b32c
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:31:15.727179+00:00
-- url     : https://prove2.me/theorems/e850372e-cc37-5d10-a838-e0482c0b9602
-- title:
--   P2 M Multi Period coupling Set  weak P nonempty 46c7c592b32c: P2 M Multi Period coupling Set  weak P nonempty 46c7c592b32c
-- statement:
--   The initial coupling set, reindexed over `WeakP (X 0 × Y 0)`, is
--       nonempty: the independent coupling `μ₀.prod ν₀` is a probability measure
--       with the prescribed marginals (F1).
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/LscBellman.lean#L581-L588
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/LscBellman.lean#L581-L588

import Definitions.Def_BicausalOT_MeasurableStrategy
import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsUHC
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LscIntegral
import Definitions.Def_BicausalOT_DescriptiveSetTheory_MeasurableSelection
import Definitions.Def_BicausalOT_LscBellman
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal
noncomputable section
open MultiPeriod
variable {X Y : ℕ → Type*}
  [∀ n, TopologicalSpace (X n)] [∀ n, PolishSpace (X n)]
  [∀ n, MeasurableSpace (X n)] [∀ n, BorelSpace (X n)]
  [∀ n, TopologicalSpace (Y n)] [∀ n, PolishSpace (Y n)]
  [∀ n, MeasurableSpace (Y n)] [∀ n, BorelSpace (Y n)]
variable (κμP : (t : ℕ) → XHist X t → ProbabilityMeasure (X (t + 1)))
variable (κνP : (t : ℕ) → YHist Y t → ProbabilityMeasure (Y (t + 1)))
variable (c : (t : ℕ) → PairHist X Y t → ℝ≥0∞)
omit [∀ n, TopologicalSpace (X n)] [∀ n, PolishSpace (X n)]
  [∀ n, BorelSpace (X n)] [∀ n, TopologicalSpace (Y n)]
  [∀ n, BorelSpace (Y n)]

theorem P2M_MultiPeriod_couplingSet__weakP_nonempty_46c7c592b32c
    (μ₀ : Measure (X 0)) [IsProbabilityMeasure μ₀]
    (ν₀ : Measure (Y 0)) [IsProbabilityMeasure ν₀] :
    {γ : WeakP (X 0 × Y 0) | γ.toMeasure ∈ CouplingSet₀ μ₀ ν₀}.Nonempty := by sorry

alias «MultiPeriod».«couplingSet₀_weakP_nonempty» := P2M_MultiPeriod_couplingSet__weakP_nonempty_46c7c592b32c
