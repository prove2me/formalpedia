-- Prove2me | Theorems.Thm_ThreeSum_TernaryWantedLittleEndian_wantedCodes_length
-- name    : ThreeSum.TernaryWantedLittleEndian.wantedCodes_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:39:16.489133+00:00
-- url     : https://prove2.me/theorems/1bee622b-1f94-4bac-8812-39da2cd27ebf
-- title:
--   Ternary Wanted Little Endian: wanted Codes length
-- statement:
--   The Ternary Wanted Little Endian construction uses the wanted Codes length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedLittleEndian.lean#L14-L17
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedLittleEndian.lean#L14-L17

import Definitions.Def_Submission_ThreeSum_TernaryWantedCanonicalPairs
import Definitions.Def_Submission_ThreeSum_TernaryWantedLittleEndian
import Theorems.Thm_ThreeSum_TernaryWantedCanonicalPairs_wantedCodes_length
import Theorems.Thm_ThreeSum_TernaryWantedCanonical_wantedCodes_length
import Theorems.Thm_ThreeSum_TernaryWantedRadix_wantedCodes_length
attribute [local simp] ThreeSum.TernaryWantedCanonical.wantedCodes_length
attribute [local simp] ThreeSum.TernaryWantedCanonicalPairs.wantedCodes_length


set_option autoImplicit false
open ThreeSum ThreeSum.TernaryWantedLittleEndian
open TernaryWantedRadix

theorem ThreeSum.TernaryWantedLittleEndian.wantedCodes_length (p : ℤ) (raws : List ℤ) (words maps : List ℕ) (j : ℕ)
    (x : ℤ) (R S code scale mapCode mapScale : ℕ) :
    (wantedCodes p raws words maps j x R S code scale mapCode mapScale).length=
      (wantedOutputs p raws j x).length := by sorry
