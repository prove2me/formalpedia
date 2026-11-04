-- Prove2me | Theorems.Thm_ThreeSum_BandEnumeration_Family_lookup_sound_w3sum_ac885d1
-- name    : ThreeSum.BandEnumeration.Family.lookup_sound_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:10:57.434062+00:00
-- url     : https://prove2.me/theorems/a936bf72-c2b6-40e2-8903-124c181ce160
-- title:
--   Family: lookup sound
-- statement:
--   The Family construction uses the lookup sound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandEnumeration.lean#L41-L53
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandEnumeration.lean#L41-L53

import Definitions.Def_Submission_ThreeSum_Bands
import Definitions.Def_Submission_ThreeSum_BinarySearch
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Nodup
import Definitions.Def_Submission_ThreeSum_BandEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.BandEnumeration
open ThreeSum.BandEnumeration.Family

theorem ThreeSum.BandEnumeration.Family.lookup_sound_w3sum_ac885d1 (A : Family) (x : ℤ) (i : A.Index)
    (h : A.lookup x = some i) : A.lo i ≤ x ∧ x ≤ A.hi i := by sorry
