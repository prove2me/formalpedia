-- Prove2me | Theorems.Thm_ThreeSum_TernaryPhysicalEuler_predRank_canonical
-- name    : ThreeSum.TernaryPhysicalEuler.predRank_canonical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:57:55.078393+00:00
-- url     : https://prove2.me/theorems/47c0473a-aba2-4d1a-88b2-23296be1f892
-- title:
--   Ternary Physical Euler: pred Rank canonical
-- statement:
--   The Ternary Physical Euler construction uses the pred Rank canonical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalEuler.lean#L47-L53
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalEuler.lean#L47-L53

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

theorem ThreeSum.TernaryPhysicalEuler.predRank_canonical {N : ℕ} (R : TritWord N) (i : Fin N) (hi : 0<(R i).val) :
    LightTernaryPredecessor.predRank N (LightTernaryEulerMetadata.lowAt N i.val)
      (LightTernaryEulerMetadata.highAt N i.val) (address R)=rank (predecessor R i) := by sorry
