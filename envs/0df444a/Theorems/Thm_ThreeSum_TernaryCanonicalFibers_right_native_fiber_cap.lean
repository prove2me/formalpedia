-- Prove2me | Theorems.Thm_ThreeSum_TernaryCanonicalFibers_right_native_fiber_cap
-- name    : ThreeSum.TernaryCanonicalFibers.right_native_fiber_cap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:38:15.846204+00:00
-- url     : https://prove2.me/theorems/64c1408e-aa7a-4435-bdb9-0b126708bd7b
-- title:
--   Ternary Canonical Fibers: right native fiber cap
-- statement:
--   The Ternary Canonical Fibers construction uses the right native fiber cap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCanonicalFibers.lean#L15-L55
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCanonicalFibers.lean#L15-L55

import Definitions.Def_Submission_ThreeSum_TernaryCanonicalDictionaries
import Definitions.Def_Submission_ThreeSum_TernaryWantedRadix
import Definitions.Def_Submission_ThreeSum_TernaryCanonicalFibers
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCanonicalFibers
open Finset TernaryFixedDictionaries TernaryCanonicalDictionaries TernaryJointType TernaryCoverLocal
variable {L p : ℕ} [Fact p.Prime] {α : DigitType}
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem ThreeSum.TernaryCanonicalFibers.right_native_fiber_cap (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (B : ℕ) (hp : 2 < p) (a : ZMod p) :
    (rightNativeFiber (α := α) maps B a).card ≤ Fintype.card I*B := by sorry
