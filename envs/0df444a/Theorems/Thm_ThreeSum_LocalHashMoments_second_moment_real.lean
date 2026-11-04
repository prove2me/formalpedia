-- Prove2me | Theorems.Thm_ThreeSum_LocalHashMoments_second_moment_real
-- name    : ThreeSum.LocalHashMoments.second_moment_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:23:24.138424+00:00
-- url     : https://prove2.me/theorems/e321103f-f118-45fd-b073-f9c3d1433b20
-- title:
--   Local Hash Moments: second moment real
-- statement:
--   The Local Hash Moments construction uses the second moment real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalHashMoments.lean#L106-L128
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalHashMoments.lean#L106-L128

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

theorem ThreeSum.LocalHashMoments.second_moment_real (hsep : 2 * h < L)
    (hDelta : degree L h ≤ Fintype.card K)
    (hG : groupSize h ≤ Fintype.card K)
    (hE : outputCount L h * groupSize h ≤ Fintype.card K ^ 2)
    (target : K × K) (B : ℕ) :
    (∑ w, (hitCount L h B w target : ℝ) ^ 2) ≤
      5 * mean L h (Fintype.card K) * Fintype.card (Weight L K) := by sorry
