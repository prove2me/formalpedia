-- Prove2me | Theorems.Thm_P2M_MultiPeriod_iInf_couplingSet__eq_iInf_weakP_9d2e42b6cc02
-- name    : P2M_MultiPeriod_iInf_couplingSet__eq_iInf_weakP_9d2e42b6cc02
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:31:34.069077+00:00
-- url     : https://prove2.me/theorems/399f9788-c09b-4cee-b4e7-cfbb62cd8e27
-- title:
--   P2 M Multi Period i Inf coupling Set  eq i Inf weak P 9d2e42b6cc02: P2 M Multi Period i Inf coupling Set  eq i Inf weak P 9d2e42b6cc02
-- statement:
--   **Reindexing bridge for the initial couplings.**  The infimum over
--       `CouplingSet₀ μ₀ ν₀ ⊆ Measure (X 0 × Y 0)` equals the infimum over the
--       Polish space `WeakP (X 0 × Y 0)` of probability measures satisfying the
--       same marginal constraints: legitimate because a coupling of probability
--       marginals is itself a probability measure (`CouplingSet₀.measure_univ`).
--       The `CouplingSet₀` analogue of `iInf_feas_eq_iInf_feasGraph`.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/LscBellman.lean#L551-L563
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/LscBellman.lean#L551-L563

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

theorem P2M_MultiPeriod_iInf_couplingSet__eq_iInf_weakP_9d2e42b6cc02
    (μ₀ : Measure (X 0)) [IsProbabilityMeasure μ₀] (ν₀ : Measure (Y 0))
    (f : X 0 × Y 0 → ℝ≥0∞) :
    (⨅ (γ₀ : Measure (X 0 × Y 0)) (_ : γ₀ ∈ CouplingSet₀ μ₀ ν₀),
        ∫⁻ h₀, f h₀ ∂γ₀)
      = ⨅ (γ : WeakP (X 0 × Y 0)) (_ : γ.toMeasure ∈ CouplingSet₀ μ₀ ν₀),
          ∫⁻ h₀, f h₀ ∂γ.toMeasure := by sorry

alias «MultiPeriod».«iInf_couplingSet₀_eq_iInf_weakP» := P2M_MultiPeriod_iInf_couplingSet__eq_iInf_weakP_9d2e42b6cc02
