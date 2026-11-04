-- Prove2me | Theorems.Thm_ThreeSum_TernaryEuler_weight_split
-- name    : ThreeSum.TernaryEuler.weight_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:37:45.49898+00:00
-- url     : https://prove2.me/theorems/38046988-9896-46fe-9822-af2cf69ab228
-- title:
--   Ternary Euler: weight split
-- statement:
--   The Ternary Euler construction uses the weight split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEuler.lean#L34-L37
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEuler.lean#L34-L37

import Definitions.Def_Submission_ThreeSum_TernaryQuery
import Definitions.Def_Submission_ThreeSum_TernaryEuler
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryEuler
open Finset
open ThreeSum.TernaryJointType ThreeSum.TernaryBank

theorem ThreeSum.TernaryEuler.weight_split {N : ℕ} (R A : TritWord N) (i : Fin N) :
    weight R A = digitChoose (R i) (A i) *
      ∏ j ∈ (univ : Finset (Fin N)).erase i, digitChoose (R j) (A j) := by sorry
