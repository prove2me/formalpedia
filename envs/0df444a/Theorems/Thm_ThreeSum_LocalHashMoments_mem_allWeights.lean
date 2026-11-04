-- Prove2me | Theorems.Thm_ThreeSum_LocalHashMoments_mem_allWeights
-- name    : ThreeSum.LocalHashMoments.mem_allWeights
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:23:25.960391+00:00
-- url     : https://prove2.me/theorems/39f5a8d8-d74a-4137-ab25-90cf3149138d
-- title:
--   Local Hash Moments: mem all Weights
-- statement:
--   The Local Hash Moments construction uses the mem all Weights property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalHashMoments.lean#L214-L218
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalHashMoments.lean#L214-L218

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

theorem ThreeSum.LocalHashMoments.mem_allWeights (values : List K) (hvalues : ∀ x, x ∈ values)
    (w : Weight L K) : w ∈ allWeights L values := by sorry
