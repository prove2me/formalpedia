-- Prove2me | Theorems.Thm_ThreeSum_TernaryWantedCanonicalPairs_wantedCodes_length
-- name    : ThreeSum.TernaryWantedCanonicalPairs.wantedCodes_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:33:56.072653+00:00
-- url     : https://prove2.me/theorems/335b14fb-0cca-49f3-a799-5071fc670fa4
-- title:
--   Ternary Wanted Canonical Pairs: wanted Codes length
-- statement:
--   The Ternary Wanted Canonical Pairs construction uses the wanted Codes length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedCanonicalPairs.lean#L12-L15
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedCanonicalPairs.lean#L12-L15

import Definitions.Def_Submission_ThreeSum_TernaryWantedCanonical
import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_TernaryWantedCanonicalPairs
import Theorems.Thm_ThreeSum_TernaryWantedCanonical_wantedCodes_length
import Theorems.Thm_ThreeSum_TernaryWantedRadix_wantedCodes_length
attribute [local simp] ThreeSum.TernaryWantedCanonical.wantedCodes_length


set_option autoImplicit false
open ThreeSum ThreeSum.TernaryWantedCanonicalPairs
open TernaryWantedRadix

theorem ThreeSum.TernaryWantedCanonicalPairs.wantedCodes_length (p : ℤ) (raws : List ℤ) (words maps : List ℕ) (j : ℕ)
    (x : ℤ) (code R mapCode S : ℕ) :
    (wantedCodes p raws words maps j x code R mapCode S).length=(wantedOutputs p raws j x).length := by sorry
