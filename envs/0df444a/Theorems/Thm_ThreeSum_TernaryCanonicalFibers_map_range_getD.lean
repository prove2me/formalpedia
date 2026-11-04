-- Prove2me | Theorems.Thm_ThreeSum_TernaryCanonicalFibers_map_range_getD
-- name    : ThreeSum.TernaryCanonicalFibers.map_range_getD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:55:06.593058+00:00
-- url     : https://prove2.me/theorems/ca6b9d1f-e8e9-41f6-9e5b-41d9ffb46c86
-- title:
--   Ternary Canonical Fibers: map range get D
-- statement:
--   The Ternary Canonical Fibers construction uses the map range get D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCanonicalFibers.lean#L58-L62
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCanonicalFibers.lean#L58-L62

import Definitions.Def_Submission_ThreeSum_TernaryCanonicalDictionaries
import Definitions.Def_Submission_ThreeSum_TernaryWantedRadix
import Definitions.Def_Submission_ThreeSum_TernaryCanonicalFibers
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCanonicalFibers
open Finset TernaryFixedDictionaries TernaryCanonicalDictionaries TernaryJointType TernaryCoverLocal
variable {L p : ℕ} [Fact p.Prime] {α : DigitType}
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem ThreeSum.TernaryCanonicalFibers.map_range_getD {A : Type*} (xs : List A) (fallback : A) :
    (List.range xs.length).map (fun i => xs.getD i fallback)=xs := by sorry
