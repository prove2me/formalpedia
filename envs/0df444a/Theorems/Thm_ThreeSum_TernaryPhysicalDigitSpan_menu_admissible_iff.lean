-- Prove2me | Theorems.Thm_ThreeSum_TernaryPhysicalDigitSpan_menu_admissible_iff
-- name    : ThreeSum.TernaryPhysicalDigitSpan.menu_admissible_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:29:09.627714+00:00
-- url     : https://prove2.me/theorems/0a44a894-a505-4da4-b163-8d0ca39ae146
-- title:
--   Ternary Physical Digit Span: menu admissible iff
-- statement:
--   The Ternary Physical Digit Span construction uses the menu admissible iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalDigitSpan.lean#L86-L90
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalDigitSpan.lean#L86-L90

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

theorem ThreeSum.TernaryPhysicalDigitSpan.menu_admissible_iff (ℓ : E →ₗ[K] K) (rows : List (Fin J → K)) (seed : E×E) :
    seed∈TernaryOriginalRowMenu.admissible (J+2) ℓ (forbidden rows) ↔
      physicalDigits (TernaryOriginalRowMenu.seedRow (J+2) ℓ seed)∉oldSpan (rows.map (reversal J)) := by sorry
