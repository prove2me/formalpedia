-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXErrorPullback_snapshot_two_run
-- name    : QEC.Coding.BDL26RXErrorPullback.snapshot_two_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T10:03:40.080053+00:00
-- url     : https://prove2.me/theorems/6edfd1d1-6cf3-4eaf-b0ed-e819b72e9369
-- title:
--   BDL26 RXError Pullback: snapshot two run
-- statement:
--   Genuine history inputs supply source errors internally; the lower error and
--   full potential are then obtained from the actual two-run theorem.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXErrorPullback.lean#L318-L361
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXErrorPullback.lean#L318-L361

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Indexed
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXErrorPullback_EmbeddedReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXErrorPullback
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXErrorPullback
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge BDL26RXCohomology BDL26AlternatingCochain
open BDL26RZCohomology (mem_cocycle_iff mem_boundary_iff)
open MultiscaleDecoder BDL26OwnerIncidenceMasks
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
variable (n : Nat) (sigma : BDL26CanonicalHistoryMarks.Input S n) (k : StepIndex n)

theorem QEC.Coding.BDL26RXErrorPullback.snapshot_two_run (sigmaB : BDL26CanonicalHistoryMarks.Input S n)
    (h : (LevelTwoHistory.physicalStep k).val % 2 = 0) :
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
