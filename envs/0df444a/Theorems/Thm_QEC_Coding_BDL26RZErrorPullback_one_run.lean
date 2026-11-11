-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZErrorPullback_one_run
-- name    : QEC.Coding.BDL26RZErrorPullback.one_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:12:50.359893+00:00
-- url     : https://prove2.me/theorems/b19545ed-2e56-4b34-9ec2-6fdbce5670a2
-- title:
--   BDL26 RZError Pullback: one run
-- statement:
--   Direct one-run update, rather than silently discarding the zero-run correction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZErrorPullback.lean#L214-L224
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZErrorPullback.lean#L214-L224

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

theorem QEC.Coding.BDL26RZErrorPullback.one_run (_above : 2 ≤ i.val) (h : ¬ i.val % 2 = 0) (a : Upper S depth i) :
    ∃ (l : Lower S depth i) (p : Potential S depth i),
      ((indexedDecoderData S depth).selectedMap i).map1 l =
        a + (run S depth i h a).correction + (indexedFamily S depth).coboundary0 i.succ p ∧
      (indexedFamily S depth).coboundary1 i.castSucc l = (run S depth i h a).coarse.val ∧
      ((indexedDecoderData S depth).selectedMap i).map2 (run S depth i h a).coarse.val =
        (indexedFamily S depth).coboundary1 i.succ (a + (run S depth i h a).correction) ∧
      (indexedFamily S depth).coboundary1 i.succ
        ((indexedFamily S depth).coboundary0 i.succ p) = 0 := by sorry
