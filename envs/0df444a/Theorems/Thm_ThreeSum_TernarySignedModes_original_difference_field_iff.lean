-- Prove2me | Theorems.Thm_ThreeSum_TernarySignedModes_original_difference_field_iff
-- name    : ThreeSum.TernarySignedModes.original_difference_field_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:42:18.898982+00:00
-- url     : https://prove2.me/theorems/48ac9edc-e558-453a-a2d3-37f38fa2d091
-- title:
--   Ternary Signed Modes: original difference field iff
-- statement:
--   The Ternary Signed Modes construction uses the original difference field iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedModes.lean#L110-L118
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedModes.lean#L110-L118

import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
import Mathlib.Data.Int.Lemmas
import Definitions.Def_Submission_ThreeSum_TernarySignedModes
set_option autoImplicit false
open ThreeSum ThreeSum.TernarySignedModes
open TernarySignedDigits TernarySignedReduction Finset

theorem ThreeSum.TernarySignedModes.original_difference_field_iff {p U radix J : ℕ} {a b c : ℤ}
    (hb : 1 < radix) (hp : 2*radix<p)
    (ha : |a| ≤ (U : ℤ)) (hB : |b| ≤ (U : ℤ)) (hC : |c| ≤ (U : ℤ))
    (hcap : 4*U<radix^J) :
    c-b=a ↔ ∃ carry ∈ carryCatalog J,
      ∀ k, fieldLeft p U radix J b k+fieldRight p U radix J c k=
        fieldRequester p U radix J a carry k := by sorry
