-- Prove2me | Theorems.Thm_ThreeSum_TernaryCanonicalFibers_source_tuple_fiber_cap
-- name    : ThreeSum.TernaryCanonicalFibers.source_tuple_fiber_cap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:08:12.001636+00:00
-- url     : https://prove2.me/theorems/525c1229-2e6b-46ec-ac4d-b0358d120c05
-- title:
--   Ternary Canonical Fibers: source tuple fiber cap
-- statement:
--   The Ternary Canonical Fibers construction uses the source tuple fiber cap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCanonicalFibers.lean#L141-L147
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCanonicalFibers.lean#L141-L147

import Definitions.Def_Submission_ThreeSum_TernaryCanonicalDictionaries
import Definitions.Def_Submission_ThreeSum_TernaryWantedRadix
import Definitions.Def_Submission_ThreeSum_TernaryCanonicalFibers
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCanonicalFibers
open Finset TernaryFixedDictionaries TernaryCanonicalDictionaries TernaryJointType TernaryCoverLocal
variable {L p : ℕ} [Fact p.Prime] {α : DigitType}
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem ThreeSum.TernaryCanonicalFibers.source_tuple_fiber_cap (right : Bool)
    (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (B : ℕ) (hp : 2 < p) (J : ℕ) (x : ℤ) :
    (TernaryWantedRadix.wantedOutputs (p : ℤ)
      ((records (α := α) right maps B).map (native right maps)) J x).length ≤
      (Fintype.card I*B)^J := by sorry
