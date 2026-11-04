-- Prove2me | Theorems.Thm_ThreeSum_TernaryPhysicalEuler_rowKey_near
-- name    : ThreeSum.TernaryPhysicalEuler.rowKey_near
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:57:43.64422+00:00
-- url     : https://prove2.me/theorems/1cdeca4f-7259-485f-a4af-50a30687b7da
-- title:
--   Ternary Physical Euler: row Key near
-- statement:
--   The Ternary Physical Euler construction uses the row Key near property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalEuler.lean#L83-L89
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalEuler.lean#L83-L89

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

theorem ThreeSum.TernaryPhysicalEuler.rowKey_near {N nb nn T bv nv : ℕ} (R : TritWord N)
    (bankWords nearWords : ℕ → TritWord N) (i : Fin N) (hi : 0<(R i).val)
    (hr : T<rank (predecessor R i)) :
    rowKey R bankWords nearWords nb nn T bv nv i.val=
      nv+ordinal nearWords nn (predecessor R i) := by sorry
