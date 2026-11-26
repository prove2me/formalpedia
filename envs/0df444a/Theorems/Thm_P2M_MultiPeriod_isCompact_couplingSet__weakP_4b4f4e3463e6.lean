-- Prove2me | Theorems.Thm_P2M_MultiPeriod_isCompact_couplingSet__weakP_4b4f4e3463e6
-- name    : P2M_MultiPeriod_isCompact_couplingSet__weakP_4b4f4e3463e6
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:31:36.914947+00:00
-- url     : https://prove2.me/theorems/95bdc97a-447b-4439-9eaa-227ab51b2a8c
-- title:
--   P2 M Multi Period is Compact coupling Set  weak P 4b4f4e3463e6: P2 M Multi Period is Compact coupling Set  weak P 4b4f4e3463e6
-- statement:
--   The initial coupling set, reindexed over `WeakP (X 0 × Y 0)`, is compact
--       in the topology of weak convergence: couplings of two fixed marginals on
--       Borel Polish spaces form a compact set
--       (`isCompact_probabilityMeasure_marginals`, which is unconditional in the
--       two target measures).
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/LscBellman.lean#L570-L573
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/LscBellman.lean#L570-L573

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

theorem P2M_MultiPeriod_isCompact_couplingSet__weakP_4b4f4e3463e6
    (μ₀ : Measure (X 0)) (ν₀ : Measure (Y 0)) :
    IsCompact {γ : WeakP (X 0 × Y 0) | γ.toMeasure ∈ CouplingSet₀ μ₀ ν₀} := by sorry

alias «MultiPeriod».«isCompact_couplingSet₀_weakP» := P2M_MultiPeriod_isCompact_couplingSet__weakP_4b4f4e3463e6
