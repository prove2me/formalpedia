-- Prove2me | Theorems.Thm_ThreeSum_TernarySignedModes_fieldMode_physical_sound
-- name    : ThreeSum.TernarySignedModes.fieldMode_physical_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:42:26.73008+00:00
-- url     : https://prove2.me/theorems/ea91f70a-ecd9-4b41-8069-b380148e8124
-- title:
--   Ternary Signed Modes: field Mode physical sound
-- statement:
--   The Ternary Signed Modes construction uses the field Mode physical sound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedModes.lean#L143-L152
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedModes.lean#L143-L152

import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
import Mathlib.Data.Int.Lemmas
import Definitions.Def_Submission_ThreeSum_TernarySignedModes
set_option autoImplicit false
open ThreeSum ThreeSum.TernarySignedModes
open TernarySignedDigits TernarySignedReduction Finset

theorem ThreeSum.TernarySignedModes.fieldMode_physical_sound {p U radix J : ℕ} {b c b' c' : ℤ}
    (hb : 1 < radix) (hp : 2*radix<p)
    (hB : |b| ≤ (U : ℤ)) (hC : |c| ≤ (U : ℤ))
    (hB' : |b'| ≤ (U : ℤ)) (hC' : |c'| ≤ (U : ℤ))
    (hcap : 4*U<radix^J)
    (hmode : ∀ k, fieldMode p U radix J b c k=fieldMode p U radix J b' c' k) :
    c-b=c'-b' := by sorry
