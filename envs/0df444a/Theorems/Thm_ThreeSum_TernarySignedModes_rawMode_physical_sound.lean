-- Prove2me | Theorems.Thm_ThreeSum_TernarySignedModes_rawMode_physical_sound
-- name    : ThreeSum.TernarySignedModes.rawMode_physical_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:42:19.592816+00:00
-- url     : https://prove2.me/theorems/3ec34e59-a535-421e-b8a5-1879fd42e982
-- title:
--   Ternary Signed Modes: raw Mode physical sound
-- statement:
--   The Ternary Signed Modes construction uses the raw Mode physical sound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedModes.lean#L120-L141
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedModes.lean#L120-L141

import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
import Mathlib.Data.Int.Lemmas
import Definitions.Def_Submission_ThreeSum_TernarySignedModes
set_option autoImplicit false
open ThreeSum ThreeSum.TernarySignedModes
open TernarySignedDigits TernarySignedReduction Finset

theorem ThreeSum.TernarySignedModes.rawMode_physical_sound {U radix J : ℕ} {b c b' c' : ℤ}
    (hB : |b| ≤ (U : ℤ)) (hC : |c| ≤ (U : ℤ))
    (hB' : |b'| ≤ (U : ℤ)) (hC' : |c'| ≤ (U : ℤ))
    (hcap : 4*U<radix^J)
    (hmode : ∀ k, rawMode U radix J b c k=rawMode U radix J b' c' k) :
    c-b=c'-b' := by sorry
