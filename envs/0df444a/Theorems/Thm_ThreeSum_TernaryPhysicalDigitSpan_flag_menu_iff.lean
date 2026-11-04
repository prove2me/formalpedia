-- Prove2me | Theorems.Thm_ThreeSum_TernaryPhysicalDigitSpan_flag_menu_iff
-- name    : ThreeSum.TernaryPhysicalDigitSpan.flag_menu_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:28:54.303379+00:00
-- url     : https://prove2.me/theorems/f7b7cc95-f7a5-4a99-a243-94d135f8142e
-- title:
--   Ternary Physical Digit Span: flag menu iff
-- statement:
--   The Ternary Physical Digit Span construction uses the flag menu iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalDigitSpan.lean#L94-L99
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalDigitSpan.lean#L94-L99

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

theorem ThreeSum.TernaryPhysicalDigitSpan.flag_menu_iff [Algebra (ZMod p) E] (ℓ : E →ₗ[ZMod p] ZMod p) (rows : List (Fin J → ZMod p)) (seed : E×E) :
    LightStoredSpan.admissibleFlag (rows.map (reversal J))
      (physicalDigits (TernaryOriginalRowMenu.seedRow (J+2) ℓ seed))=1 ↔
      seed∈TernaryOriginalRowMenu.admissible (J+2) ℓ (forbidden rows) := by sorry
