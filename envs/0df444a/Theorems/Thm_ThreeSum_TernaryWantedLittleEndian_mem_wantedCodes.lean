-- Prove2me | Theorems.Thm_ThreeSum_TernaryWantedLittleEndian_mem_wantedCodes
-- name    : ThreeSum.TernaryWantedLittleEndian.mem_wantedCodes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:54:35.975436+00:00
-- url     : https://prove2.me/theorems/f02257e7-84c8-49e1-b090-0366da22a2f9
-- title:
--   Ternary Wanted Little Endian: mem wanted Codes
-- statement:
--   The Ternary Wanted Little Endian construction uses the mem wanted Codes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedLittleEndian.lean#L44-L51
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedLittleEndian.lean#L44-L51

import Definitions.Def_Submission_ThreeSum_TernaryWantedCanonicalPairs
import Definitions.Def_Submission_ThreeSum_TernaryWantedLittleEndian
import Theorems.Thm_ThreeSum_TernaryWantedCanonicalPairs_mem_wantedCodes

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryWantedLittleEndian
open TernaryWantedRadix

theorem ThreeSum.TernaryWantedLittleEndian.mem_wantedCodes {p : ℤ} (hp : p ≠ 0) (raws : List ℤ) (words maps : List ℕ)
    (j : ℕ) (x : ℤ) (R S code scale mapCode mapScale w f : ℕ) :
    (w,f) ∈ wantedCodes p raws words maps j x R S code scale mapCode mapScale ↔
      ∃ is : List ℕ, is.length=j ∧ (∀ i ∈ is, i<raws.length) ∧
        p^j ∣ x-Radix.positionalHash p (fun i => raws.getD i 0) is ∧
        encode words R code scale is=w ∧ encode maps S mapCode mapScale is=f := by sorry
