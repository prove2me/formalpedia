-- Prove2me | Theorems.Thm_ThreeSum_TernaryCanonicalFibers_native_filter_cap
-- name    : ThreeSum.TernaryCanonicalFibers.native_filter_cap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:38:30.768825+00:00
-- url     : https://prove2.me/theorems/adbe4fbd-9ca7-45ac-ab93-f2a2fdb2fa72
-- title:
--   Ternary Canonical Fibers: native filter cap
-- statement:
--   The concrete trimmed table pays for every occurrence, including maps
--   with identical coefficients and vertices with equal integer key labels.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCanonicalFibers.lean#L85-L131
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCanonicalFibers.lean#L85-L131

import Definitions.Def_Submission_ThreeSum_TernaryCanonicalDictionaries
import Definitions.Def_Submission_ThreeSum_TernaryWantedRadix
import Definitions.Def_Submission_ThreeSum_TernaryCanonicalFibers
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCanonicalFibers
open Finset TernaryFixedDictionaries TernaryCanonicalDictionaries TernaryJointType TernaryCoverLocal
variable {L p : ℕ} [Fact p.Prime] {α : DigitType}
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem ThreeSum.TernaryCanonicalFibers.native_filter_cap (right : Bool)
    (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (B : ℕ) (hp : 2 < p) (x : ℤ) :
    ((records (α := α) right maps B).filter
      (fun r => (p : ℤ) ∣ x-native right maps r)).length ≤ Fintype.card I*B := by sorry
