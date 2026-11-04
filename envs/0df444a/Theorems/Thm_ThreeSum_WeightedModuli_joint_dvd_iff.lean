-- Prove2me | Theorems.Thm_ThreeSum_WeightedModuli_joint_dvd_iff
-- name    : ThreeSum.WeightedModuli.joint_dvd_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:18:57.150057+00:00
-- url     : https://prove2.me/theorems/e74af192-5498-47bc-923c-bcea772c1ef4
-- title:
--   Weighted Moduli: joint dvd iff
-- statement:
--   The Weighted Moduli construction uses the joint dvd iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WeightedModuli.lean#L31-L40
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WeightedModuli.lean#L31-L40

import Definitions.Def_Submission_ThreeSum_Auxiliary
import Definitions.Def_Submission_ThreeSum_WeightedModuli
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedModuli
open Finset Arithmetic
open scoped BigOperators

theorem ThreeSum.WeightedModuli.joint_dvd_iff (q p : ℕ) (hp : Nat.Prime p) (z : ℤ) :
    (joint q p : ℤ) ∣ z ↔ (q : ℤ) ∣ z ∧ (p : ℤ) ∣ z := by sorry
