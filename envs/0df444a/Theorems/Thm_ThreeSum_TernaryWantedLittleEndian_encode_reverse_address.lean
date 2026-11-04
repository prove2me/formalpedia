-- Prove2me | Theorems.Thm_ThreeSum_TernaryWantedLittleEndian_encode_reverse_address
-- name    : ThreeSum.TernaryWantedLittleEndian.encode_reverse_address
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:10:03.866568+00:00
-- url     : https://prove2.me/theorems/b02a335a-540c-4fa9-80b8-817f63bb747a
-- title:
--   Ternary Wanted Little Endian: encode reverse address
-- statement:
--   The runtime accumulates least-native-position first. Canonical addresses
--   are high-first, so the corresponding word reverses block order, not digits.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedLittleEndian.lean#L29-L42
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedLittleEndian.lean#L29-L42

import Definitions.Def_Submission_ThreeSum_TernaryWantedCanonicalPairs
import Definitions.Def_Submission_ThreeSum_TernaryWantedLittleEndian
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryWantedLittleEndian
open TernaryWantedRadix

theorem ThreeSum.TernaryWantedLittleEndian.encode_reverse_address (L : ℕ) (localWords : ℕ → List ℕ) (digits : List ℕ)
    (hblocks : ∀ i, (localWords i).length=L)
    (hdigits : ∀ i, digits.getD i 0=TernaryAddresses.code (localWords i)) :
    ∀ (is : List ℕ) (code scale : ℕ),
      encode digits (4^L) code scale is = code+scale*
        TernaryAddresses.code (is.reverse.flatMap localWords) := by sorry
