-- Prove2me | Theorems.Thm_ThreeSum_TernaryWantedCanonical_wantedCodes_length
-- name    : ThreeSum.TernaryWantedCanonical.wantedCodes_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:28:23.215282+00:00
-- url     : https://prove2.me/theorems/1301fe71-8494-47d8-980c-ef9e0b933fe2
-- title:
--   Ternary Wanted Canonical: wanted Codes length
-- statement:
--   The Ternary Wanted Canonical construction uses the wanted Codes length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedCanonical.lean#L16-L19
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedCanonical.lean#L16-L19

import Definitions.Def_Submission_ThreeSum_TernaryWantedRadix
import Definitions.Def_Submission_ThreeSum_TernaryWantedCanonical
import Theorems.Thm_ThreeSum_TernaryWantedRadix_wantedCodes_length

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryWantedCanonical
open TernaryWantedRadix

theorem ThreeSum.TernaryWantedCanonical.wantedCodes_length (p : ℤ) (raws : List ℤ) (digits : List ℕ)
    (j : ℕ) (x : ℤ) (code R : ℕ) :
    (wantedCodes p raws digits j x code R).length=(wantedOutputs p raws j x).length := by sorry
