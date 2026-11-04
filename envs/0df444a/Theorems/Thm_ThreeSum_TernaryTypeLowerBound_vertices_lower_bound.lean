-- Prove2me | Theorems.Thm_ThreeSum_TernaryTypeLowerBound_vertices_lower_bound
-- name    : ThreeSum.TernaryTypeLowerBound.vertices_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:59:32.761542+00:00
-- url     : https://prove2.me/theorems/8f434054-dc1b-4080-9f98-d32898cbb998
-- title:
--   Ternary Type Lower Bound: vertices lower bound
-- statement:
--   Two-way choices for 1-digits and three-way choices for 2-digits give
--   an explicit subfamily of the required output type.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryTypeLowerBound.lean#L70-L107
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryTypeLowerBound.lean#L70-L107

import Definitions.Def_Submission_ThreeSum_TernaryCoverOutputCap
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryTypeLowerBound
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryTypeLowerBound
open Finset TernaryJointType TernaryCoverLocal

theorem ThreeSum.TernaryTypeLowerBound.vertices_lower_bound {L : ℕ} (π : DigitType)
    (htotal : π 0+π 1+π 2 = L) (hspace : 2*(π 1)+3*(π 2) ≤ L) :
    2^(π 1)*3^(π 2) ≤ (vertices L π).card := by sorry
