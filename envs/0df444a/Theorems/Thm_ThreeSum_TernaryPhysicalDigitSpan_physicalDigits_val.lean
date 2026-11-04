-- Prove2me | Theorems.Thm_ThreeSum_TernaryPhysicalDigitSpan_physicalDigits_val
-- name    : ThreeSum.TernaryPhysicalDigitSpan.physicalDigits_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:29:13.21122+00:00
-- url     : https://prove2.me/theorems/4f587ad9-d3c4-40e8-97f0-b4b1ebf073ee
-- title:
--   Ternary Physical Digit Span: physical Digits val
-- statement:
--   The backend's first J physical cells are the logical digit projection
--   followed by reversal; the two unrestricted tag cells never enter this row.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalDigitSpan.lean#L103-L109
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalDigitSpan.lean#L103-L109

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
variable {E : Type*} [Field E] [Algebra K E] [Fintype K] [Fintype E] [DecidableEq K] [DecidableEq E]
variable {p : ℕ} [Fact p.Prime]

theorem ThreeSum.TernaryPhysicalDigitSpan.physicalDigits_val (row : Fin (J+2) → K) (i : Fin J) :
    physicalDigits row i=row ⟨J-1-i.val,by have := i.isLt; omega⟩ := by sorry
