-- Prove2me | Theorems.Thm_ThreeSum_LocalHashMoments_second_moment
-- name    : ThreeSum.LocalHashMoments.second_moment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:23:24.397405+00:00
-- url     : https://prove2.me/theorems/68316cba-5278-43c7-b66b-223c0cc3c2f8
-- title:
--   Local Hash Moments: second moment
-- statement:
--   The Local Hash Moments construction uses the second moment property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalHashMoments.lean#L75-L85
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalHashMoments.lean#L75-L85

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

theorem ThreeSum.LocalHashMoments.second_moment (hsep : 2 * h < L)
    (hDelta : degree L h ≤ Fintype.card K)
    (hG : groupSize h ≤ Fintype.card K)
    (hE : outputCount L h * groupSize h ≤ Fintype.card K ^ 2)
    (target : K × K) (B : ℕ) :
    Fintype.card K ^ 2 * (∑ w, hitCount L h B w target ^ 2) ≤
      5 * Fintype.card (Edge L h) * Fintype.card (Weight L K) := by sorry
