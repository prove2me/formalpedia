-- Prove2me | Theorems.Thm_ThreeSum_TernaryWantedCanonicalPairs_encode_append_address
-- name    : ThreeSum.TernaryWantedCanonicalPairs.encode_append_address
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:48:34.967205+00:00
-- url     : https://prove2.me/theorems/b3d844bf-904c-4ca0-ba07-fd933590f134
-- title:
--   Ternary Wanted Canonical Pairs: encode append address
-- statement:
--   The Ternary Wanted Canonical Pairs construction uses the encode append address property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedCanonicalPairs.lean#L61-L75
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedCanonicalPairs.lean#L61-L75

import Definitions.Def_Submission_ThreeSum_TernaryWantedCanonical
import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_TernaryWantedCanonicalPairs
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryWantedCanonicalPairs
open TernaryWantedRadix

theorem ThreeSum.TernaryWantedCanonicalPairs.encode_append_address (L : ℕ) (localWords : ℕ → List ℕ) (digits : List ℕ)
    (hblocks : ∀ i, (localWords i).length=L)
    (hdigits : ∀ i, digits.getD i 0=TernaryAddresses.code (localWords i)) :
    ∀ (is : List ℕ) (preword : List ℕ),
      TernaryWantedCanonical.encode digits (4^L) (TernaryAddresses.code preword) is=
        TernaryAddresses.code (preword++blockWords localWords is) := by sorry
