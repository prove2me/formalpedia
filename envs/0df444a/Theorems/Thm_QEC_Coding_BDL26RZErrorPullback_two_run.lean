-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZErrorPullback_two_run
-- name    : QEC.Coding.BDL26RZErrorPullback.two_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:09:59.638733+00:00
-- url     : https://prove2.me/theorems/d4574677-1dbd-41ed-869d-debcb6000d7b
-- title:
--   BDL26 RZError Pullback: two run
-- statement:
--   The full two-run result, with no caller-supplied lower error or potential.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZErrorPullback.lean#L198-L211
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZErrorPullback.lean#L198-L211

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology_Indexed
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZErrorPullback
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RZErrorPullback
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge BDL26RZCohomology BDL26AlternatingCochain
open MultiscaleDecoder BDL26OwnerIncidenceMasks
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)

theorem QEC.Coding.BDL26RZErrorPullback.two_run (_above : 2 ≤ i.val) (h : ¬ i.val % 2 = 0) (a b : Upper S depth i) :
    ∃ (l : Lower S depth i) (p : Potential S depth i),
      ((indexedDecoderData S depth).selectedMap i).map1 l =
        a + b + (run S depth i h a).correction + (run S depth i h b).correction +
          (indexedFamily S depth).coboundary0 i.succ p ∧
      (indexedFamily S depth).coboundary1 i.castSucc l =
        (run S depth i h a).coarse.val + (run S depth i h b).coarse.val ∧
      ((indexedDecoderData S depth).selectedMap i).map2
        ((run S depth i h a).coarse.val + (run S depth i h b).coarse.val) =
          (indexedFamily S depth).coboundary1 i.succ (updated S depth i h a b) ∧
      (indexedFamily S depth).coboundary1 i.succ
        ((indexedFamily S depth).coboundary0 i.succ p) = 0 := by sorry
