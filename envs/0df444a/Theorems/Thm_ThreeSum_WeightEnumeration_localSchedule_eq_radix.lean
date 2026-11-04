-- Prove2me | Theorems.Thm_ThreeSum_WeightEnumeration_localSchedule_eq_radix
-- name    : ThreeSum.WeightEnumeration.localSchedule_eq_radix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:46:38.990463+00:00
-- url     : https://prove2.me/theorems/3bb52084-1773-46f0-9af8-8801d4720976
-- title:
--   Weight Enumeration: local Schedule eq radix
-- statement:
--   Rewriting the schedule preserves its precise tie rule and every chosen
--   map occurrence because the candidate lists are equal in order.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WeightEnumeration.lean#L198-L207
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WeightEnumeration.lean#L198-L207

import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Mathlib.Data.List.Range
import Definitions.Def_Submission_ThreeSum_WeightEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.WeightEnumeration
open LocalHashMoments
variable {ι K : Type*} [DecidableEq ι] [NatCast K]

theorem ThreeSum.WeightEnumeration.localSchedule_eq_radix (h : ℕ) :
    localSchedule h =
      Cover.greedyChoices
        ((List.range ((LocalCoverBounds.localPrime h)^(2*(512*h)))).map
          (decodedWeight (K := LocalField h) (512*h) (LocalCoverBounds.localPrime h)))
        (Covers (512*h) h (bucketBound (512*h) h (Fintype.card (LocalField h))))
        (Finset.univ : Finset (LocalField h × LocalField h))
        (scheduleLength h (Fintype.card (LocalField h))) := by sorry
