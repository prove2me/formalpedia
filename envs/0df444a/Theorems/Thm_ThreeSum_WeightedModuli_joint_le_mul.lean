-- Prove2me | Theorems.Thm_ThreeSum_WeightedModuli_joint_le_mul
-- name    : ThreeSum.WeightedModuli.joint_le_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:18:55.738333+00:00
-- url     : https://prove2.me/theorems/38b12679-2590-4cf9-b3a4-59ad6fdafcf0
-- title:
--   Weighted Moduli: joint le mul
-- statement:
--   The Weighted Moduli construction uses the joint le mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WeightedModuli.lean#L18-L22
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WeightedModuli.lean#L18-L22

import Definitions.Def_Submission_ThreeSum_Auxiliary
import Definitions.Def_Submission_ThreeSum_WeightedModuli
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedModuli
open Finset Arithmetic
open scoped BigOperators

theorem ThreeSum.WeightedModuli.joint_le_mul (q p : ℕ) (hp : 1 ≤ p) : joint q p ≤ q * p := by sorry
