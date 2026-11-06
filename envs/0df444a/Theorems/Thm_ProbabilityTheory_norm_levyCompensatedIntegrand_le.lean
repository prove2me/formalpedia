-- Prove2me | Theorems.Thm_ProbabilityTheory_norm_levyCompensatedIntegrand_le
-- name    : ProbabilityTheory.norm_levyCompensatedIntegrand_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T12:13:09.016045+00:00
-- url     : https://prove2.me/theorems/4e6d6642-e208-4115-8755-f682948e5787
-- title:
--   LeanLevy: ProbabilityTheory.norm_levyCompensatedIntegrand_le
-- statement:
--   The compensated integrand norm is bounded by `(2 + 3 * ξ²) · min(1, x²)`. The exact theorem type was printed from the pinned compiled Lean environment; the source proof remains to be transplanted and remotely verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/CompensatedIntegral.lean#L97

import Mathlib
import Definitions.Def_LeanLevy_Levy_CompensatedIntegral
open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal BigOperators

theorem ProbabilityTheory.norm_levyCompensatedIntegrand_le :
  ∀ (ξ x : ℝ), ‖ProbabilityTheory.levyCompensatedIntegrand ξ x‖ ≤ (2 + 3 * ξ ^ 2) * min 1 (x ^ 2) := by sorry
