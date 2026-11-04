-- Prove2me | Theorems.Thm_ThreeSum_TernaryPhysicalDigitSpan_oldSpan_proper
-- name    : ThreeSum.TernaryPhysicalDigitSpan.oldSpan_proper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:29:31.04573+00:00
-- url     : https://prove2.me/theorems/b9304181-6373-47ff-ab98-8e2c3b566f70
-- title:
--   Ternary Physical Digit Span: old Span proper
-- statement:
--   The Ternary Physical Digit Span construction uses the old Span proper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalDigitSpan.lean#L59-L73
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalDigitSpan.lean#L59-L73

import Definitions.Def_Submission_ThreeSum_LightStoredSpan
import Definitions.Def_Submission_ThreeSum_TernaryOriginalRowMenu
import Definitions.Def_Submission_ThreeSum_TernarySignedLayout
import Mathlib.LinearAlgebra.Dimension.Constructions
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalDigitSpan
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPhysicalDigitSpan
open Light
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
variable {K : Type*} [Field K] {J : ℕ}

theorem ThreeSum.TernaryPhysicalDigitSpan.oldSpan_proper (rows : List (Fin J → K)) (hlen : rows.length<J) : oldSpan rows≠⊤ := by sorry
