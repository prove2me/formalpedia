-- Prove2me | Theorems.Thm_ThreeSum_TernaryHybridCore_program_length
-- name    : ThreeSum.TernaryHybridCore.program_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:09:18.970967+00:00
-- url     : https://prove2.me/theorems/bc5351b1-7a15-4e3c-9b9c-ed18ebc8bd0e
-- title:
--   Ternary Hybrid Core: program length
-- statement:
--   The Ternary Hybrid Core construction uses the program length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryHybridCore.lean#L44-L47
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryHybridCore.lean#L44-L47

import Definitions.Def_Submission_ThreeSum_TernaryHybridResources
import Definitions.Def_Submission_ThreeSum_ReportingHostRelocation
import Definitions.Def_Submission_ThreeSum_TernaryHybridCore
import Theorems.Thm_ThreeSum_LightBruteThreeSum_program_length

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryHybridCore
open Light
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000

theorem ThreeSum.TernaryHybridCore.program_length (fastP : Program) (fastProc κ cutoff : ℕ) :
    (program fastP fastProc κ cutoff).length=fastP.length+6 := by sorry
