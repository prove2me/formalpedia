-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverCapParameters_actual_edge_pos
-- name    : ThreeSum.TernaryCoverCapParameters.actual_edge_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:50:13.123919+00:00
-- url     : https://prove2.me/theorems/39eb412e-a02a-4761-95f2-cceeeaebb05f
-- title:
--   Ternary Cover Cap Parameters: actual edge pos
-- statement:
--   The Ternary Cover Cap Parameters construction uses the actual edge pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverCapParameters.lean#L52-L61
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverCapParameters.lean#L52-L61

import Definitions.Def_Submission_ThreeSum_TernaryCoverFrequency
import Mathlib.Algebra.Order.Floor.Div
import Definitions.Def_Submission_ThreeSum_TernaryCoverCapParameters
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCoverCapParameters
open TernaryJointType TernaryCoverLocal TernaryLocalParameters
open TernaryCoverGoodMaps TernaryCoverFrequency TernaryPartitionCount TernaryTypeLowerBound

theorem ThreeSum.TernaryCoverCapParameters.actual_edge_pos (m : ℕ) : 0 < Fintype.card (ActualEdge m) := by sorry
