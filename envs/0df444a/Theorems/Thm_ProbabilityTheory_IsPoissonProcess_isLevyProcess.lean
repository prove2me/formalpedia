-- Prove2me | Theorems.Thm_ProbabilityTheory_IsPoissonProcess_isLevyProcess
-- name    : ProbabilityTheory.IsPoissonProcess.isLevyProcess
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T08:02:48.457385+00:00
-- url     : https://prove2.me/theorems/0920fd88-8f44-4aa1-a749-8b90828a0328
-- title:
--   LeanLevy: ProbabilityTheory.IsPoissonProcess.isLevyProcess
-- statement:
--   Source-header theorem from the pinned LeanLevy library. The original mathematical assertion is retained with explicit names and source-compatible universe declarations. Its original proof has not been transplanted or verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/PoissonProcess.lean#L196

import Definitions.Def_LeanLevy_Processes_PoissonProcess

open MeasureTheory Real Complex Finset ProbabilityTheory
open scoped ENNReal NNReal Nat

universe u
variable {Ω : Type u} [MeasurableSpace Ω] {N : NNReal → Ω → ℕ} {rate : NNReal} {μ : MeasureTheory.Measure Ω}

theorem ProbabilityTheory.IsPoissonProcess.isLevyProcess (h : IsPoissonProcess N rate μ)
    (hcadlag : ∀ᵐ ω ∂μ, IsCadlag (fun t => (N t ω : ℤ))) :
    IsLevyProcess (fun t ω => (N t ω : ℤ)) μ := by sorry
