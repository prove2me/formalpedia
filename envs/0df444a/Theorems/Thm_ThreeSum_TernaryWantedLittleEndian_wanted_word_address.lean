-- Prove2me | Theorems.Thm_ThreeSum_TernaryWantedLittleEndian_wanted_word_address
-- name    : ThreeSum.TernaryWantedLittleEndian.wanted_word_address
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:48:34.801198+00:00
-- url     : https://prove2.me/theorems/7a9190c3-3295-45ca-aac2-d096baaef792
-- title:
--   Ternary Wanted Little Endian: wanted word address
-- statement:
--   Integer target hashes use least-significant block first; canonical words
--   use the corresponding reversed sequence of blocks, with each block unchanged.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedLittleEndian.lean#L55-L67
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedLittleEndian.lean#L55-L67

import Definitions.Def_Submission_ThreeSum_TernaryWantedCanonicalPairs
import Definitions.Def_Submission_ThreeSum_TernaryWantedLittleEndian
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryWantedLittleEndian
open TernaryWantedRadix

theorem ThreeSum.TernaryWantedLittleEndian.wanted_word_address {p : ℤ} (raws : List ℤ) (localWords : ℕ → List ℕ)
    (digits maps : List ℕ) (L J S : ℕ) (x : ℤ) (w f : ℕ)
    (hp : p ≠ 0) (hblocks : ∀ i, (localWords i).length=L)
    (hdigits : ∀ i, digits.getD i 0=TernaryAddresses.code (localWords i))
    (h : (w,f) ∈ wantedCodes p raws digits maps J x (4^L) S 0 1 0 1) :
    ∃ is : List ℕ, is.length=J ∧ (∀ i ∈ is, i<raws.length) ∧
      p^J ∣ x-Radix.positionalHash p (fun i => raws.getD i 0) is ∧
      w=TernaryAddresses.code (is.reverse.flatMap localWords) ∧
      f=encode maps S 0 1 is := by sorry
