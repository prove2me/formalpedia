-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_values_bounded
-- name    : ThreeSum.BandRawA.values_bounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:27:06.373429+00:00
-- url     : https://prove2.me/theorems/b8180199-d4ad-4d1b-89e9-f571d089b7c7
-- title:
--   Band Raw A: values bounded
-- statement:
--   The Band Raw A construction uses the values bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawA.lean#L143-L148
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawA.lean#L143-L148

import Definitions.Def_Submission_ThreeSum_BandCandidateRowsMemory
import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_BandRawA
import Definitions.Def_WeightedCache3SUM_Alias_f8621e0ea40777d9

set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows BandEnumeration BandPartition
set_option maxHeartbeats 1600000
set_option maxRecDepth 7000

theorem ThreeSum.BandRawA.values_bounded {n g i U : ℕ} {rs : List Record} {f : ℕ → ℤ}
    (hf : ∀ j < n, |f j| ≤ (U : ℤ)) :
    ∀ v ∈ values f (firstRows n g rs i), |v| ≤ (U : ℤ) := by sorry
