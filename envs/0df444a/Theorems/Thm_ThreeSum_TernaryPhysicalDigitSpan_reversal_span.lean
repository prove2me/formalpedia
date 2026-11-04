-- Prove2me | Theorems.Thm_ThreeSum_TernaryPhysicalDigitSpan_reversal_span
-- name    : ThreeSum.TernaryPhysicalDigitSpan.reversal_span
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:29:34.123931+00:00
-- url     : https://prove2.me/theorems/bdc67cd2-2c8d-402f-8487-eb411171c2e7
-- title:
--   Ternary Physical Digit Span: reversal span
-- statement:
--   The Ternary Physical Digit Span construction uses the reversal span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalDigitSpan.lean#L46-L53
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalDigitSpan.lean#L46-L53

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

theorem ThreeSum.TernaryPhysicalDigitSpan.reversal_span (rows : List (Fin J → K)) (row : Fin J → K) :
    reversal J row∈oldSpan (rows.map (reversal J)) ↔ row∈oldSpan rows := by sorry
