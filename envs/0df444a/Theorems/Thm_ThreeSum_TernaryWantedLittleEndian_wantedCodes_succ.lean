-- Prove2me | Theorems.Thm_ThreeSum_TernaryWantedLittleEndian_wantedCodes_succ
-- name    : ThreeSum.TernaryWantedLittleEndian.wantedCodes_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:44:50.192214+00:00
-- url     : https://prove2.me/theorems/facc354d-70ae-4520-8d68-d431717dd42e
-- title:
--   Ternary Wanted Little Endian: wanted Codes succ
-- statement:
--   The Ternary Wanted Little Endian construction uses the wanted Codes succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedLittleEndian.lean#L19-L25
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedLittleEndian.lean#L19-L25

import Definitions.Def_Submission_ThreeSum_TernaryWantedCanonicalPairs
import Definitions.Def_Submission_ThreeSum_TernaryWantedLittleEndian
import Theorems.Thm_ThreeSum_TernaryWantedCanonicalPairs_wantedCodes_succ
import Theorems.Thm_ThreeSum_TernaryWantedCanonical_wantedCodes_succ
import Theorems.Thm_ThreeSum_TernaryWantedRadix_wantedCodes_succ

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryWantedLittleEndian
open TernaryWantedRadix

theorem ThreeSum.TernaryWantedLittleEndian.wantedCodes_succ (p : ℤ) (raws : List ℤ) (words maps : List ℕ) (j : ℕ)
    (x : ℤ) (R S code scale mapCode mapScale : ℕ) :
    wantedCodes p raws words maps (j+1) x R S code scale mapCode mapScale =
      (localBucket p raws x).flatMap fun i => wantedCodes p raws words maps j
        ((x-raws.getD i 0)/p) R S (code+scale*words.getD i 0) (scale*R)
          (mapCode+mapScale*maps.getD i 0) (mapScale*S) := by sorry
