-- Prove2me | Theorems.Thm_ThreeSum_LightStoredSpan_program_length
-- name    : ThreeSum.LightStoredSpan.program_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:15:31.182101+00:00
-- url     : https://prove2.me/theorems/2c2e0d64-524e-4760-b271-34812675ae91
-- title:
--   Light Stored Span: program length
-- statement:
--   The Light Stored Span construction uses the program length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightStoredSpan.lean#L102-L102
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightStoredSpan.lean#L102-L102

import Definitions.Def_Submission_ThreeSum_TernaryStoredSpan
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Copy
import Definitions.Def_Submission_ThreeSum_LightStoredSpan
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightStoredSpan
open Light ThreeSum.TernaryStoredSpan
set_option maxHeartbeats 5000000
set_option maxRecDepth 12000
attribute [local instance] Classical.propDecidable
variable {lim : Limits} {P : Program} {p J : ℕ} [Fact p.Prime]

theorem ThreeSum.LightStoredSpan.program_length : program.length=8 := by sorry

attribute [defeq] ThreeSum.LightStoredSpan.program_length
