-- Prove2me | Theorems.Thm_ThreeSum_TernaryPhysicalDigitSpan_physical_span_iff
-- name    : ThreeSum.TernaryPhysicalDigitSpan.physical_span_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:29:25.132552+00:00
-- url     : https://prove2.me/theorems/200e9664-3b92-4a26-989c-b1e03f83ac11
-- title:
--   Ternary Physical Digit Span: physical span iff
-- statement:
--   The Ternary Physical Digit Span construction uses the physical span iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalDigitSpan.lean#L55-L57
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalDigitSpan.lean#L55-L57

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

theorem ThreeSum.TernaryPhysicalDigitSpan.physical_span_iff (rows : List (Fin J → K)) (row : Fin (J+2) → K) :
    physicalDigits row∈oldSpan (rows.map (reversal J)) ↔ row∈forbidden rows := by sorry
