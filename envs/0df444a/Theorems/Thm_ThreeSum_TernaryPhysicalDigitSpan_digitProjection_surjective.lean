-- Prove2me | Theorems.Thm_ThreeSum_TernaryPhysicalDigitSpan_digitProjection_surjective
-- name    : ThreeSum.TernaryPhysicalDigitSpan.digitProjection_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:29:19.02981+00:00
-- url     : https://prove2.me/theorems/a6aa702c-132a-4711-98f0-911553c8d46e
-- title:
--   Ternary Physical Digit Span: digit Projection surjective
-- statement:
--   The Ternary Physical Digit Span construction uses the digit Projection surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalDigitSpan.lean#L40-L44
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalDigitSpan.lean#L40-L44

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

theorem ThreeSum.TernaryPhysicalDigitSpan.digitProjection_surjective : Function.Surjective (digitProjection (K := K) J) := by sorry
