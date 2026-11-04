-- Prove2me | Theorems.Thm_ThreeSum_TernaryOriginalCollisions_deleted_card_le_collisions
-- name    : ThreeSum.TernaryOriginalCollisions.deleted_card_le_collisions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:20:45.709211+00:00
-- url     : https://prove2.me/theorems/761a7a56-173b-45d9-a4d0-17acf727fbb7
-- title:
--   Ternary Original Collisions: deleted card le collisions
-- statement:
--   The Ternary Original Collisions construction uses the deleted card le collisions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalCollisions.lean#L24-L33
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalCollisions.lean#L24-L33

import Definitions.Def_Submission_ThreeSum_TernaryOriginalRowMenu
import Definitions.Def_Submission_ThreeSum_TernaryOriginalCollisions
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryOriginalCollisions
open Finset TernaryOriginalRowMenu
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {K E B W : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Field E] [Algebra K E] [Fintype E] [DecidableEq E]
  [Fintype B] [DecidableEq B] [DecidableEq W]

theorem ThreeSum.TernaryOriginalCollisions.deleted_card_le_collisions (hash : B → W) :
    (deleted hash).card ≤ (collisionPairs hash).card := by sorry
