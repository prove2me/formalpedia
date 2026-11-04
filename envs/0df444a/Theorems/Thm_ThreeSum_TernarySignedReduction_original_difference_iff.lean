-- Prove2me | Theorems.Thm_ThreeSum_TernarySignedReduction_original_difference_iff
-- name    : ThreeSum.TernarySignedReduction.original_difference_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:37:56.362187+00:00
-- url     : https://prove2.me/theorems/6877ea01-2247-4fcc-b3dc-894aa5eff851
-- title:
--   Ternary Signed Reduction: original difference iff
-- statement:
--   All original signed inputs, both directions, with literal finite carries.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedReduction.lean#L105-L116
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedReduction.lean#L105-L116

import Definitions.Def_Submission_ThreeSum_TernarySignedDigits
import Mathlib.Data.ZMod.Basic
import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
set_option autoImplicit false
open ThreeSum ThreeSum.TernarySignedReduction
open TernarySignedDigits Finset

theorem ThreeSum.TernarySignedReduction.original_difference_iff {U radix J : ℕ} {a b c : ℤ}
    (ha : |a| ≤ (U : ℤ)) (hb : |b| ≤ (U : ℤ)) (hc : |c| ≤ (U : ℤ))
    (hcap : 4*U<radix^J) :
    c-b=a ↔ ∃ carry ∈ carryCatalog J,
      ∀ k, leftRaw U radix J b k+rightRaw U radix J c k=requesterRaw U radix J a carry k := by sorry
