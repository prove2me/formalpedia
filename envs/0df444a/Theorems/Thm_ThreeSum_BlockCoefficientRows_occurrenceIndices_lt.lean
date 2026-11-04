-- Prove2me | Theorems.Thm_ThreeSum_BlockCoefficientRows_occurrenceIndices_lt
-- name    : ThreeSum.BlockCoefficientRows.occurrenceIndices_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:48:35.806205+00:00
-- url     : https://prove2.me/theorems/00a42343-843f-400c-95fd-cc6647972212
-- title:
--   Block Coefficient Rows: occurrence Indices lt
-- statement:
--   The Block Coefficient Rows construction uses the occurrence Indices lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockCoefficientRows.lean#L68-L70
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockCoefficientRows.lean#L68-L70

import Definitions.Def_Submission_ThreeSum_LightBlockCoefficients
import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
set_option autoImplicit false
open ThreeSum ThreeSum.BlockCoefficientRows
open BlockRows BlockIndex BlockEncoding GlobalEncoding LocalCoverBounds

theorem ThreeSum.BlockCoefficientRows.occurrenceIndices_lt {h J : ℕ} (o : Occurrences h J) {j : ℕ} (hj : j < J) :
    occurrenceIndices o j < scheduleSize h := by sorry
