-- Prove2me | Theorems.Thm_ThreeSum_TernaryWantedCanonical_wantedCodes_succ
-- name    : ThreeSum.TernaryWantedCanonical.wantedCodes_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:29:14.232905+00:00
-- url     : https://prove2.me/theorems/aef8628f-4c8b-4b50-ab85-e8b228439fde
-- title:
--   Ternary Wanted Canonical: wanted Codes succ
-- statement:
--   The Ternary Wanted Canonical construction uses the wanted Codes succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedCanonical.lean#L21-L25
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedCanonical.lean#L21-L25

import Definitions.Def_Submission_ThreeSum_TernaryWantedRadix
import Definitions.Def_Submission_ThreeSum_TernaryWantedCanonical
import Theorems.Thm_ThreeSum_TernaryWantedRadix_wantedCodes_succ

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryWantedCanonical
open TernaryWantedRadix

theorem ThreeSum.TernaryWantedCanonical.wantedCodes_succ (p : ℤ) (raws : List ℤ) (digits : List ℕ)
    (j : ℕ) (x : ℤ) (code R : ℕ) :
    wantedCodes p raws digits (j+1) x code R = (localBucket p raws x).flatMap fun i =>
      wantedCodes p raws digits j ((x-raws.getD i 0)/p) (code*R+digits.getD i 0) R := by sorry
