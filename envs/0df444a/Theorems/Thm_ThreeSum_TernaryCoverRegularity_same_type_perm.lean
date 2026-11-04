-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverRegularity_same_type_perm
-- name    : ThreeSum.TernaryCoverRegularity.same_type_perm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:05:49.838209+00:00
-- url     : https://prove2.me/theorems/70f32c1d-85e3-4a14-8dbc-e696f7bd2d53
-- title:
--   Ternary Cover Regularity: same type perm
-- statement:
--   All words of the same type lie in one coordinate-permutation orbit.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRegularity.lean#L23-L34
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRegularity.lean#L23-L34

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryCoverRegularity
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverRegularity
open Finset TernaryJointType TernaryCoverLocal
variable {L : ℕ}

theorem ThreeSum.TernaryCoverRegularity.same_type_perm {a b : TritWord L} {α : DigitType}
    (ha : HasType a α) (hb : HasType b α) :
    ∃ σ : Equiv.Perm (Fin L), reindex σ a = b := by sorry
