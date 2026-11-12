-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZErrorPullback_snapshot_two_run
-- name    : QEC.Coding.BDL26RZErrorPullback.snapshot_two_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T10:30:32.915467+00:00
-- url     : https://prove2.me/theorems/726dc2ec-32c0-4379-acb1-9b003f8d9cf6
-- title:
--   BDL26 RZError Pullback: snapshot two run
-- statement:
--   Genuine history inputs supply source errors internally; the lower error and
--   full potential are then obtained from the actual two-run theorem.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZErrorPullback.lean#L254-L297
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZErrorPullback.lean#L254-L297

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
variable (n : Nat) (sigma : BDL26CanonicalHistoryMarks.Input S n) (k : StepIndex n)

theorem QEC.Coding.BDL26RZErrorPullback.snapshot_two_run (sigmaB : BDL26CanonicalHistoryMarks.Input S n)
    (h : ¬ (LevelTwoHistory.physicalStep k).val % 2 = 0) :
    ∃ (a b : Upper S (n + 2) (LevelTwoHistory.physicalStep k))
      (l : Lower S (n + 2) (LevelTwoHistory.physicalStep k))
      (p : Potential S (n + 2) (LevelTwoHistory.physicalStep k)),
      (indexedFamily S (n + 2)).coboundary1 (LevelTwoHistory.physicalStep k).succ a =
        (BDL26CanonicalHistoryMarks.inputAt S n sigma k.succ).val ∧
      (indexedFamily S (n + 2)).coboundary1 (LevelTwoHistory.physicalStep k).succ b =
        (BDL26CanonicalHistoryMarks.inputAt S n sigmaB k.succ).val ∧
      ((indexedDecoderData S (n + 2)).selectedMap (LevelTwoHistory.physicalStep k)).map1 l =
        a + b + (BDL26CanonicalHistoryMarks.outputAt S n sigma k).correction +
          (BDL26CanonicalHistoryMarks.outputAt S n sigmaB k).correction +
            (indexedFamily S (n + 2)).coboundary0 (LevelTwoHistory.physicalStep k).succ p ∧
      (indexedFamily S (n + 2)).coboundary1 (LevelTwoHistory.physicalStep k).castSucc l =
        (BDL26CanonicalHistoryMarks.outputAt S n sigma k).coarse.val +
          (BDL26CanonicalHistoryMarks.outputAt S n sigmaB k).coarse.val ∧
      ((indexedDecoderData S (n + 2)).selectedMap (LevelTwoHistory.physicalStep k)).map2
        ((BDL26CanonicalHistoryMarks.outputAt S n sigma k).coarse.val +
          (BDL26CanonicalHistoryMarks.outputAt S n sigmaB k).coarse.val) =
        (indexedFamily S (n + 2)).coboundary1 (LevelTwoHistory.physicalStep k).succ
          (a + b + (BDL26CanonicalHistoryMarks.outputAt S n sigma k).correction +
            (BDL26CanonicalHistoryMarks.outputAt S n sigmaB k).correction) ∧
      (indexedFamily S (n + 2)).coboundary1 (LevelTwoHistory.physicalStep k).succ
        ((indexedFamily S (n + 2)).coboundary0 (LevelTwoHistory.physicalStep k).succ p) = 0 := by sorry
