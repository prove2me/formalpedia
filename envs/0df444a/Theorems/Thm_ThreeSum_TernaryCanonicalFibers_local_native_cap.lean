-- Prove2me | Theorems.Thm_ThreeSum_TernaryCanonicalFibers_local_native_cap
-- name    : ThreeSum.TernaryCanonicalFibers.local_native_cap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:06:00.310204+00:00
-- url     : https://prove2.me/theorems/fe496a8e-62e6-4024-8751-87428e343aa6
-- title:
--   Ternary Canonical Fibers: local native cap
-- statement:
--   The Ternary Canonical Fibers construction uses the local native cap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCanonicalFibers.lean#L133-L139
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCanonicalFibers.lean#L133-L139

import Definitions.Def_Submission_ThreeSum_TernaryCanonicalDictionaries
import Definitions.Def_Submission_ThreeSum_TernaryWantedRadix
import Definitions.Def_Submission_ThreeSum_TernaryCanonicalFibers
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCanonicalFibers
open Finset TernaryFixedDictionaries TernaryCanonicalDictionaries TernaryJointType TernaryCoverLocal
variable {L p : ℕ} [Fact p.Prime] {α : DigitType}
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem ThreeSum.TernaryCanonicalFibers.local_native_cap (right : Bool)
    (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (B : ℕ) (hp : 2 < p) (x : ℤ) :
    (TernaryWantedRadix.localBucket (p : ℤ)
      ((records (α := α) right maps B).map (native right maps)) x).length ≤ Fintype.card I*B := by sorry
