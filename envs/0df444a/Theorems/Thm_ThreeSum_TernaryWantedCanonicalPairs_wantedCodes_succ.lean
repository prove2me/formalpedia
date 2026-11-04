-- Prove2me | Theorems.Thm_ThreeSum_TernaryWantedCanonicalPairs_wantedCodes_succ
-- name    : ThreeSum.TernaryWantedCanonicalPairs.wantedCodes_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:37:37.68701+00:00
-- url     : https://prove2.me/theorems/b1ec4874-1eb1-4755-ab62-85a0748dc926
-- title:
--   Ternary Wanted Canonical Pairs: wanted Codes succ
-- statement:
--   The Ternary Wanted Canonical Pairs construction uses the wanted Codes succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedCanonicalPairs.lean#L17-L23
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedCanonicalPairs.lean#L17-L23

import Definitions.Def_Submission_ThreeSum_TernaryWantedCanonical
import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_TernaryWantedCanonicalPairs
import Theorems.Thm_ThreeSum_TernaryWantedCanonical_wantedCodes_succ
import Theorems.Thm_ThreeSum_TernaryWantedRadix_wantedCodes_succ

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryWantedCanonicalPairs
open TernaryWantedRadix

theorem ThreeSum.TernaryWantedCanonicalPairs.wantedCodes_succ (p : ℤ) (raws : List ℤ) (words maps : List ℕ) (j : ℕ)
    (x : ℤ) (code R mapCode S : ℕ) :
    wantedCodes p raws words maps (j+1) x code R mapCode S =
      (localBucket p raws x).flatMap fun i =>
        wantedCodes p raws words maps j ((x-raws.getD i 0)/p)
          (code*R+words.getD i 0) R (mapCode*S+maps.getD i 0) S := by sorry
