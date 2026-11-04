-- Prove2me | Theorems.Thm_ThreeSum_TernaryWantedCanonicalPairs_mem_wantedCodes
-- name    : ThreeSum.TernaryWantedCanonicalPairs.mem_wantedCodes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:26:48.403196+00:00
-- url     : https://prove2.me/theorems/e6371a2e-3e63-4e03-8b55-68c6782ffe69
-- title:
--   Ternary Wanted Canonical Pairs: mem wanted Codes
-- statement:
--   The Ternary Wanted Canonical Pairs construction uses the mem wanted Codes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedCanonicalPairs.lean#L39-L47
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedCanonicalPairs.lean#L39-L47

import Definitions.Def_Submission_ThreeSum_TernaryWantedCanonical
import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_TernaryWantedCanonicalPairs
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryWantedCanonicalPairs
open TernaryWantedRadix

theorem ThreeSum.TernaryWantedCanonicalPairs.mem_wantedCodes {p : ℤ} (hp : p ≠ 0) (raws : List ℤ) (words maps : List ℕ)
    (j : ℕ) (x : ℤ) (code R mapCode S : ℕ) (w f : ℕ) :
    (w,f) ∈ wantedCodes p raws words maps j x code R mapCode S ↔
      ∃ is : List ℕ, is.length=j ∧ (∀ i ∈ is, i<raws.length) ∧
        p^j ∣ x-Radix.positionalHash p (fun i => raws.getD i 0) is ∧
        TernaryWantedCanonical.encode words R code is=w ∧
        TernaryWantedCanonical.encode maps S mapCode is=f := by sorry
