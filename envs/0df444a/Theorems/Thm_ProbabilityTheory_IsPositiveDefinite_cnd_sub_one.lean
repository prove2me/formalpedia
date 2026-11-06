-- Prove2me | Theorems.Thm_ProbabilityTheory_IsPositiveDefinite_cnd_sub_one
-- name    : ProbabilityTheory.IsPositiveDefinite.cnd_sub_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:19:20.948331+00:00
-- url     : https://prove2.me/theorems/19a1f84e-9e3f-4db3-92f7-5c3cc8ccd4e4
-- title:
--   LeanLevy: ProbabilityTheory.IsPositiveDefinite.cnd_sub_one
-- statement:
--   Source-header theorem from the pinned LeanLevy library. The source section variables are declared in the preamble. Its original proof has not been transplanted or verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean#L437

import Init
import Mathlib.Data.Complex.Basic
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof

theorem ProbabilityTheory.IsPositiveDefinite.cnd_sub_one {g : ℝ → ℂ} (hg : IsPositiveDefinite g) :
    IsConditionallyNegativeDefinite (fun ξ => g ξ - 1) := by sorry
