-- Prove2me | Theorems.Thm_ProbabilityTheory_IsLevyMeasure_isLevyMeasure_iff
-- name    : ProbabilityTheory.IsLevyMeasure.isLevyMeasure_iff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T12:33:42.614309+00:00
-- url     : https://prove2.me/theorems/b1fe453f-ee91-4966-adb6-6b7b44670dc2
-- title:
--   LeanLevy: ProbabilityTheory.IsLevyMeasure.isLevyMeasure_iff
-- statement:
--   Exact theorem signature transcribed from the pinned LeanLevy source. The source section variable is made explicit; the proof remains open.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyMeasure.lean#L54

import Mathlib
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory Complex ComplexConjugate Finset Filter Topology Matrix ProbabilityTheory ProbabilityTheory.IsLevyMeasure

theorem ProbabilityTheory.IsLevyMeasure.isLevyMeasure_iff {ν : Measure ℝ} :
    IsLevyMeasure ν ↔ ν {0} = 0 ∧ ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν < ⊤ := by sorry
