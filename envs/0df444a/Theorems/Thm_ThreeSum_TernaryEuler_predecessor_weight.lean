-- Prove2me | Theorems.Thm_ThreeSum_TernaryEuler_predecessor_weight
-- name    : ThreeSum.TernaryEuler.predecessor_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:37:45.394402+00:00
-- url     : https://prove2.me/theorems/10364c56-2ee3-4eae-9eb6-849c55735b2b
-- title:
--   Ternary Euler: predecessor weight
-- statement:
--   The Ternary Euler construction uses the predecessor weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEuler.lean#L39-L47
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEuler.lean#L39-L47

import Definitions.Def_Submission_ThreeSum_TernaryQuery
import Definitions.Def_Submission_ThreeSum_TernaryEuler
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryEuler
open Finset
open ThreeSum.TernaryJointType ThreeSum.TernaryBank

theorem ThreeSum.TernaryEuler.predecessor_weight {N : ℕ} (R A : TritWord N) (i : Fin N) :
    weight (predecessor R i) A = digitChoose (predDigit (R i)) (A i) *
      ∏ j ∈ (univ : Finset (Fin N)).erase i, digitChoose (R j) (A j) := by sorry
