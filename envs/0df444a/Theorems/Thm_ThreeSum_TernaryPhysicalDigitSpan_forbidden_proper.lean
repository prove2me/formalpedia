-- Prove2me | Theorems.Thm_ThreeSum_TernaryPhysicalDigitSpan_forbidden_proper
-- name    : ThreeSum.TernaryPhysicalDigitSpan.forbidden_proper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:29:09.303203+00:00
-- url     : https://prove2.me/theorems/e02c572b-d797-49c4-b6c2-6529c2108681
-- title:
--   Ternary Physical Digit Span: forbidden proper
-- statement:
--   The Ternary Physical Digit Span construction uses the forbidden proper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalDigitSpan.lean#L75-L82
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalDigitSpan.lean#L75-L82

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

theorem ThreeSum.TernaryPhysicalDigitSpan.forbidden_proper (rows : List (Fin J → K)) (hlen : rows.length<J) : forbidden rows≠⊤ := by sorry
