-- Prove2me | Theorems.Thm_ThreeSum_LocalHashMoments_local_schedule_representation_cap
-- name    : ThreeSum.LocalHashMoments.local_schedule_representation_cap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:23:28.722259+00:00
-- url     : https://prove2.me/theorems/037f2357-8bc2-49d2-a5eb-2ea7498a8a7a
-- title:
--   Local Hash Moments: local schedule representation cap
-- statement:
--   The whole selected schedule has an explicit local representation cap,
--   counting repeated chosen maps with their list multiplicity.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalHashMoments.lean#L320-L333
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalHashMoments.lean#L320-L333

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

theorem ThreeSum.LocalHashMoments.local_schedule_representation_cap (h : ℕ) (target : LocalField h × LocalField h) :
    ((localSchedule h).map (fun w => hitCount (512 * h) h (localBucketCap h) w target)).sum ≤
      (320 * (2 * h + 1) * (Nat.log2 (localPrime h ^ 2) + 1)) * localBucketCap h ^ 2 := by sorry
