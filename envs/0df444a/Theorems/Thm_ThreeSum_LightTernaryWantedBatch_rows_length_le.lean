-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryWantedBatch_rows_length_le
-- name    : ThreeSum.LightTernaryWantedBatch.rows_length_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:08:29.625679+00:00
-- url     : https://prove2.me/theorems/2325adb8-f38f-4bf3-b302-95d535e533ec
-- title:
--   Light Ternary Wanted Batch: rows length le
-- statement:
--   The Light Ternary Wanted Batch construction uses the rows length le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryWantedBatch.lean#L24-L33
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryWantedBatch.lean#L24-L33

import Definitions.Def_Submission_ThreeSum_LightTernaryWantedCanonical
import Definitions.Def_Submission_ThreeSum_LightTernaryWantedBatch
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryWantedBatch
open Light LightTernaryWantedCanonical
open TernaryWantedLittleEndian (wantedCodes)
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

theorem ThreeSum.LightTernaryWantedBatch.rows_length_le (P R S J C : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (targets : ℕ → ℤ) (positions : ℕ → ℕ)
    (hcap : ∀ x, (TernaryWantedRadix.localBucket (P : ℤ) raws x).length≤C) (n : ℕ) :
    (rows P R S J raws words maps targets positions n).length≤3*n*C^J := by sorry
