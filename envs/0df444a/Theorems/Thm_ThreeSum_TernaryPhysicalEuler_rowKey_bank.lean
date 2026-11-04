-- Prove2me | Theorems.Thm_ThreeSum_TernaryPhysicalEuler_rowKey_bank
-- name    : ThreeSum.TernaryPhysicalEuler.rowKey_bank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:57:56.793197+00:00
-- url     : https://prove2.me/theorems/f092765a-2f5d-40ab-99fa-dd6ae6b1c663
-- title:
--   Ternary Physical Euler: row Key bank
-- statement:
--   The Ternary Physical Euler construction uses the row Key bank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalEuler.lean#L75-L81
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalEuler.lean#L75-L81

import Definitions.Def_Submission_ThreeSum_LightTernaryEulerMetadata
import Definitions.Def_Submission_ThreeSum_LightTernaryEulerMemo
import Definitions.Def_Submission_ThreeSum_TernaryPartialEuler
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalEuler
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPhysicalEuler
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 3000000

theorem ThreeSum.TernaryPhysicalEuler.rowKey_bank {N nb nn T bv nv : ℕ} (R : TritWord N)
    (bankWords nearWords : ℕ → TritWord N) (i : Fin N) (hi : 0<(R i).val)
    (hr : rank (predecessor R i)≤T) :
    rowKey R bankWords nearWords nb nn T bv nv i.val=
      bv+ordinal bankWords nb (predecessor R i) := by sorry
