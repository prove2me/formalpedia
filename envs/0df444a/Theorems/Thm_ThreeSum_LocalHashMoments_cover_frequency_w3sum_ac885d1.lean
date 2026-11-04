-- Prove2me | Theorems.Thm_ThreeSum_LocalHashMoments_cover_frequency_w3sum_ac885d1
-- name    : ThreeSum.LocalHashMoments.cover_frequency_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:23:24.466782+00:00
-- url     : https://prove2.me/theorems/17ac2c4d-8994-44b5-8010-5f8f41ffd70c
-- title:
--   Local Hash Moments: cover frequency
-- statement:
--   Every target is covered by a polynomial fraction of the actual weight
--   assignments. All probabilistic premises are discharged by counting the
--   one-hot hashes on the concrete graph.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalHashMoments.lean#L133-L163
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalHashMoments.lean#L133-L163

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

theorem ThreeSum.LocalHashMoments.cover_frequency_w3sum_ac885d1 (hsep : 2 * h < L)
    (hDelta : degree L h ≤ Fintype.card K)
    (hG : groupSize h ≤ Fintype.card K)
    (hE : outputCount L h * groupSize h ≤ Fintype.card K ^ 2)
    (hupper : Fintype.card K ^ 2 ≤ 16 * (outputCount L h * 2 ^ (2 * h)))
    (target : K × K) :
    Fintype.card (Weight L K) ≤ 320 * (2 * h + 1) *
      (univ.filter fun w => Covers L h (bucketBound L h (Fintype.card K)) w target).card := by sorry
