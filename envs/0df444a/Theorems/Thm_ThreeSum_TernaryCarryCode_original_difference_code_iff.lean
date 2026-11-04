-- Prove2me | Theorems.Thm_ThreeSum_TernaryCarryCode_original_difference_code_iff
-- name    : ThreeSum.TernaryCarryCode.original_difference_code_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:00:27.600949+00:00
-- url     : https://prove2.me/theorems/068b3e4c-ceb9-488b-b24d-0b3adac7253d
-- title:
--   Ternary Carry Code: original difference code iff
-- statement:
--   The exact original equation is covered by the literal bounded integer
--   loop over carry codes, followed by its explicit lowest-bit test.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCarryCode.lean#L108-L123
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCarryCode.lean#L108-L123

import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
import Definitions.Def_Submission_ThreeSum_TernarySignedModes
import Mathlib.Data.Nat.Digits.Lemmas
import Definitions.Def_Submission_ThreeSumApsp_Util_List
import Definitions.Def_Submission_ThreeSum_TernaryCarryCode
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCarryCode
open TernarySignedDigits TernarySignedReduction Finset

theorem ThreeSum.TernaryCarryCode.original_difference_code_iff {p U radix J : ℕ} {a b c : ℤ}
    (hb : 1<radix) (hp : 2*radix<p)
    (hA : |a|≤(U : ℤ)) (hB : |b|≤(U : ℤ)) (hC : |c|≤(U : ℤ))
    (hcap : 4*U<radix^J) :
    c-b=a ↔ ∃ q<2^J, digit 2 q 0=0 ∧
      ∀ k, TernarySignedModes.fieldLeft p U radix J b k+
        TernarySignedModes.fieldRight p U radix J c k=
        TernarySignedModes.fieldRequester p U radix J a (carryFromCode J q) k := by sorry
