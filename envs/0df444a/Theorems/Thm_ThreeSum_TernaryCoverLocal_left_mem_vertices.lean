-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverLocal_left_mem_vertices
-- name    : ThreeSum.TernaryCoverLocal.left_mem_vertices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:46:57.893772+00:00
-- url     : https://prove2.me/theorems/2de52aaa-da7a-49ec-8039-2d21e0220ae4
-- title:
--   Ternary Cover Local: left mem vertices
-- statement:
--   The Ternary Cover Local construction uses the left mem vertices property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverLocal.lean#L59-L62
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverLocal.lean#L59-L62

import Definitions.Def_Submission_ThreeSum_TernaryJointType
import Definitions.Def_Submission_ThreeSum_TernaryCoverTrimming
import Definitions.Def_Submission_ThreeSum_TernaryCoverFibers
import Definitions.Def_Submission_ThreeSum_TernaryCoverRetained
import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverLocal
open Finset TernaryJointType TernaryCoverHashes
open scoped BigOperators
variable {L p : ℕ}

theorem ThreeSum.TernaryCoverLocal.left_mem_vertices {α π : DigitType} (e : LocalEdge L α π) :
    left e ∈ vertices L α := by sorry
