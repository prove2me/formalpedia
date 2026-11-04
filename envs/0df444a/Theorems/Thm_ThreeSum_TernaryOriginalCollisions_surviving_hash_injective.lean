-- Prove2me | Theorems.Thm_ThreeSum_TernaryOriginalCollisions_surviving_hash_injective
-- name    : ThreeSum.TernaryOriginalCollisions.surviving_hash_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:20:43.448252+00:00
-- url     : https://prove2.me/theorems/24ed35c0-dc90-4be5-979d-f5d2f9e8520a
-- title:
--   Ternary Original Collisions: surviving hash injective
-- statement:
--   The Ternary Original Collisions construction uses the surviving hash injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalCollisions.lean#L35-L41
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalCollisions.lean#L35-L41

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

theorem ThreeSum.TernaryOriginalCollisions.surviving_hash_injective (hash : B → W) :
    Function.Injective (fun a : {a : B // a ∉ deleted hash} => hash a.val) := by sorry
