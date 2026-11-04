-- Prove2me | Theorems.Thm_ThreeSum_LocalHashMoments_first_moment
-- name    : ThreeSum.LocalHashMoments.first_moment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:23:18.107941+00:00
-- url     : https://prove2.me/theorems/679b2ece-03c0-478f-b882-8e7854ec5418
-- title:
--   Local Hash Moments: first moment
-- statement:
--   The Local Hash Moments construction uses the first moment property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalHashMoments.lean#L61-L73
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalHashMoments.lean#L61-L73

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

theorem ThreeSum.LocalHashMoments.first_moment (hsep : 2 * h < L) (target : K × K) :
    Fintype.card (Edge L h) * Fintype.card (Weight L K) ≤
      2 * Fintype.card K ^ 2 *
        ∑ w, hitCount L h (bucketBound L h (Fintype.card K)) w target := by sorry
