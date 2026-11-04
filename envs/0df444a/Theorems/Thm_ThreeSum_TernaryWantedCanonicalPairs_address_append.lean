-- Prove2me | Theorems.Thm_ThreeSum_TernaryWantedCanonicalPairs_address_append
-- name    : ThreeSum.TernaryWantedCanonicalPairs.address_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:26:47.506245+00:00
-- url     : https://prove2.me/theorems/b65037aa-b945-49ed-ae12-9a2b551fa2d9
-- title:
--   Ternary Wanted Canonical Pairs: address append
-- statement:
--   The canonical two-bit address concatenates actual local word blocks.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedCanonicalPairs.lean#L50-L57
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedCanonicalPairs.lean#L50-L57

import Definitions.Def_Submission_ThreeSum_TernaryWantedCanonical
import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_TernaryWantedCanonicalPairs
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryWantedCanonicalPairs
open TernaryWantedRadix

theorem ThreeSum.TernaryWantedCanonicalPairs.address_append (as bs : List ℕ) :
    TernaryAddresses.code (as++bs)=
      TernaryAddresses.code as*4^bs.length+TernaryAddresses.code bs := by sorry
