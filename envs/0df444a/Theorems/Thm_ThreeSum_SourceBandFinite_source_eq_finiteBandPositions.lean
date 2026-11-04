-- Prove2me | Theorems.Thm_ThreeSum_SourceBandFinite_source_eq_finiteBandPositions
-- name    : ThreeSum.SourceBandFinite.source_eq_finiteBandPositions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:12:27.478086+00:00
-- url     : https://prove2.me/theorems/7f5e737c-25e3-46b9-a4e8-deece1479313
-- title:
--   Source Band Finite: source eq finite Band Positions
-- statement:
--   The Source Band Finite construction uses the source eq finite Band Positions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandFinite.lean#L10-L13
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandFinite.lean#L10-L13

import Definitions.Def_Submission_ThreeSum_SourceBandBankData
import Definitions.Def_Submission_ThreeSum_BandRawAFiniteSlices
import Definitions.Def_Submission_ThreeSum_SourceBandFinite
set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandFinite
open GlobalEncoding OutputDecodeRecords

theorem ThreeSum.SourceBandFinite.source_eq_finiteBandPositions (n g i : ℕ) :
    SourceBandPartition.source n g i=BandRawA.finiteBandPositions n g i := by sorry
