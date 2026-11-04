-- Prove2me | Theorems.Thm_ThreeSum_TernaryEuler_weight_euler
-- name    : ThreeSum.TernaryEuler.weight_euler
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:37:49.946191+00:00
-- url     : https://prove2.me/theorems/c9fecb7f-29a4-47e3-9a8e-2acbbf2eb324
-- title:
--   Ternary Euler: weight euler
-- statement:
--   The Ternary Euler construction uses the weight euler property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEuler.lean#L55-L59
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEuler.lean#L55-L59

import Definitions.Def_Submission_ThreeSum_TernaryQuery
import Definitions.Def_Submission_ThreeSum_TernaryEuler
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryEuler
open Finset
open ThreeSum.TernaryJointType ThreeSum.TernaryBank

theorem ThreeSum.TernaryEuler.weight_euler {N : ℕ} (R A : TritWord N) :
    (∑ i : Fin N, (R i).val * weight (predecessor R i) A) =
      ((rank R : ℤ) - (rank A : ℤ)) * weight R A := by sorry
