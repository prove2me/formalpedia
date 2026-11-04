-- Prove2me | Theorems.Thm_ThreeSum_TernarySignedModes_intCast_bounded_injective
-- name    : ThreeSum.TernarySignedModes.intCast_bounded_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:42:25.86003+00:00
-- url     : https://prove2.me/theorems/08311f20-fcde-49b3-a298-306b4b281fba
-- title:
--   Ternary Signed Modes: int Cast bounded injective
-- statement:
--   The Ternary Signed Modes construction uses the int Cast bounded injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedModes.lean#L76-L89
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedModes.lean#L76-L89

import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
import Mathlib.Data.Int.Lemmas
import Definitions.Def_Submission_ThreeSum_TernarySignedModes
set_option autoImplicit false
open ThreeSum ThreeSum.TernarySignedModes
open TernarySignedDigits TernarySignedReduction Finset

theorem ThreeSum.TernarySignedModes.intCast_bounded_injective {radix p : ℕ} {x y : ℤ}
    (hp : 2*radix<p) (hx : |x| ≤ (radix : ℤ)) (hy : |y| ≤ (radix : ℤ))
    (hxy : (x : ZMod p)=(y : ZMod p)) : x=y := by sorry
