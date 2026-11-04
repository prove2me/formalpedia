-- Prove2me | Theorems.Thm_ThreeSum_weighted_solvedInTime_96013971_50000000
-- name    : ThreeSum.weighted_solvedInTime_96013971_50000000
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T04:52:20.765392+00:00
-- url     : https://prove2.me/theorems/ed05238f-f628-47e5-b767-ee0dc6071208
-- title:
--   Three Sum: weighted solved In Time 96013971 50000000
-- statement:
--   The original deterministic word-RAM benchmark, for every fixed
--   polynomial magnitude exponent, at the exact rational exponent 96013971/50000000.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryFinalSolver.lean#L22-L28
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryFinalSolver.lean#L22-L28

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryProfileFastExecution
import Definitions.Def_Submission_Weighted_Global_TernaryFinalSolver
set_option autoImplicit false
noncomputable section
open ThreeSum
open Light WeightedGlobalConcreteProfile

theorem ThreeSum.weighted_solvedInTime_96013971_50000000 :
    EndStatement.ThreeSum.SolvedInTime (96013971/50000000 : Rat) := by sorry
