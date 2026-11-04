-- Prove2me | Theorems.Thm_ThreeSum_LocalHashMoments_cover_has_edge
-- name    : ThreeSum.LocalHashMoments.cover_has_edge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:23:27.130713+00:00
-- url     : https://prove2.me/theorems/08710dec-10a4-4e1b-ae3a-d80daba04f75
-- title:
--   Local Hash Moments: cover has edge
-- statement:
--   The Local Hash Moments construction uses the cover has edge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalHashMoments.lean#L254-L264
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalHashMoments.lean#L254-L264

import Definitions.Def_Submission_ThreeSum_HashFamily
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Definitions.Def_Submission_ThreeSum_Greedy
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.List.Pi
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Definitions.Def_Submission_ThreeSum_LocalHashMoments
set_option autoImplicit false
open ThreeSum ThreeSum.LocalHashMoments
open Finset
open scoped BigOperators
open LocalGraph LocalCoverBounds
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {L h : ℕ}

theorem ThreeSum.LocalHashMoments.cover_has_edge {B : ℕ} {w : Weight L K} {target : K × K}
    (hc : Covers L h B w target) :
    ∃ e : Edge L h, HashFamily.hashValue w (left e) = target.1 ∧
      HashFamily.hashValue w (right e) = target.2 ∧
      HashFamily.bucketSize (leftVertices L h) w target.1 ≤ B ∧
      HashFamily.bucketSize (rightVertices L h) w target.2 ≤ B := by sorry
