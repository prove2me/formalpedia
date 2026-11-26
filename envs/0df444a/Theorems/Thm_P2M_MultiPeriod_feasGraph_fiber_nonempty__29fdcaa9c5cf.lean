-- Prove2me | Theorems.Thm_P2M_MultiPeriod_feasGraph_fiber_nonempty__29fdcaa9c5cf
-- name    : P2M_MultiPeriod_feasGraph_fiber_nonempty__29fdcaa9c5cf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:30:38.145238+00:00
-- url     : https://prove2.me/theorems/e82e9b86-ddaf-446e-8ee8-9ab06f0083f6
-- title:
--   P2 M Multi Period feas Graph fiber nonempty  29fdcaa9c5cf: P2 M Multi Period feas Graph fiber nonempty  29fdcaa9c5cf
-- statement:
--   Fibers of the feasibility graph at probability kernels are nonempty
--       (product coupling, F1).
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/LscBellman.lean#L88-L94
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/LscBellman.lean#L88-L94

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
  [∀ n, PolishSpace (Y n)] [∀ n, BorelSpace (Y n)]

theorem P2M_MultiPeriod_feasGraph_fiber_nonempty__29fdcaa9c5cf (t : ℕ) (h : PairHist X Y t) :
    ∃ γ : WeakP (X (t + 1) × Y (t + 1)),
      (h, γ) ∈ FeasGraph (fun t x => (κμP t x : Measure (X (t + 1))))
        (fun t y => (κνP t y : Measure (Y (t + 1)))) t := by sorry

alias «MultiPeriod».«feasGraph_fiber_nonempty'» := P2M_MultiPeriod_feasGraph_fiber_nonempty__29fdcaa9c5cf
