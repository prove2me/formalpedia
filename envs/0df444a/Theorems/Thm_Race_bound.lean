-- Prove2me | Theorems.Thm_Race_bound
-- name    : Race.bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T00:00:11.632383+00:00
-- url     : https://prove2.me/theorems/21b55cef-541f-4a10-8c74-1280a0fe003f
-- title:
--   Race: bound
-- statement:
--   Weighted-cache refinement of the inherited deterministic ternary 3SUM
--   solver. Source credits and the original machine specification are retained.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission.lean#L6-L8
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission.lean#L6-L8

import Definitions.Def_Submission_EndStatement

set_option autoImplicit false

theorem Race.bound :
    EndStatement.ThreeSum.SolvedInTime ((96013971 : Rat) / 50000000) := by sorry
