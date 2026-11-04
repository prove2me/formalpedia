-- Prove2me | Theorems.Thm_ThreeSum_LightLocalCoverTables_entry_eq
-- name    : ThreeSum.LightLocalCoverTables.entry_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:04:45.1673+00:00
-- url     : https://prove2.me/theorems/8305d13d-49da-4da0-ae09-6e9a83e00c41
-- title:
--   Light Local Cover Tables: entry eq
-- statement:
--   The Light Local Cover Tables construction uses the entry eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverTables.lean#L35-L40
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverTables.lean#L35-L40

import Definitions.Def_Submission_ThreeSum_LightLocalCoverMatrix
import Definitions.Def_Submission_ThreeSum_LightLocalCoverSchedule
import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
import Definitions.Def_Submission_ThreeSum_LightLocalCoverTables
set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverTables
open Light LocalHashMoments LocalCoverBounds GlobalEncoding LightLocalCoverSchedule

theorem ThreeSum.LightLocalCoverTables.entry_eq (h j r : ℕ) :
    LightLocalCoverCandidate.entry (512*h) (LocalMaskGraph.vertexCount (512*h) h)
      (localPrime h) (localBucketCap h) (LocalMaskGraph.maskAt (512*h) h)
      (LocalCoverMatrix.bits (512*h) h)
      (LocalMaskHashes.coeff false (candidate h j))
      (LocalMaskHashes.coeff true (candidate h j)) r = matrix h j r := by sorry
