-- Prove2me | Theorems.Thm_ProbabilityTheory_IsCompoundPoissonDriver_ae_strictMono_arrival
-- name    : ProbabilityTheory.IsCompoundPoissonDriver.ae_strictMono_arrival
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T12:18:09.812122+00:00
-- url     : https://prove2.me/theorems/55636490-a85d-4410-8d38-fcc76e94fb7d
-- title:
--   LeanLevy: ProbabilityTheory.IsCompoundPoissonDriver.ae_strictMono_arrival
-- statement:
--   The arrival times of a compound Poisson driver are almost surely strictly increasing. The exact theorem type was printed from the pinned compiled Lean environment; the source proof remains to be transplanted and remotely verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/CompoundPoisson.lean#L145

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal BigOperators
universe u_1

theorem ProbabilityTheory.IsCompoundPoissonDriver.ae_strictMono_arrival :
  ∀ {Ω : Type u_1} [inst : MeasurableSpace Ω] {τ Y : ℕ → Ω → ℝ} {r : NNReal} {ν' : MeasureTheory.Measure ℝ}
  {μ : MeasureTheory.Measure Ω},
  ProbabilityTheory.IsCompoundPoissonDriver τ Y r ν' μ →
    0 < r → ∀ᵐ (ω : Ω) ∂μ, StrictMono fun n => ProbabilityTheory.arrival τ n ω := by sorry
