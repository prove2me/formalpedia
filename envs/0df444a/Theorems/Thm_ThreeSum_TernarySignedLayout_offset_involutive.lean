-- Prove2me | Theorems.Thm_ThreeSum_TernarySignedLayout_offset_involutive
-- name    : ThreeSum.TernarySignedLayout.offset_involutive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:22:36.900749+00:00
-- url     : https://prove2.me/theorems/6532bb64-2d73-41ed-8e45-c9789ad5d1bd
-- title:
--   Ternary Signed Layout: offset involutive
-- statement:
--   The Ternary Signed Layout construction uses the offset involutive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedLayout.lean#L15-L20
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedLayout.lean#L15-L20

import Definitions.Def_Submission_ThreeSum_LightTernarySignedRow
import Definitions.Def_Submission_ThreeSum_TernarySignedLayout
set_option autoImplicit false
open ThreeSum ThreeSum.TernarySignedLayout
open TernarySignedReduction

theorem ThreeSum.TernarySignedLayout.offset_involutive {J i : ℕ} (hi : i<J+2) : offset J (offset J i)=i := by sorry
