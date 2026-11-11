-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXErrorPullback_snapshot_output_eq
-- name    : QEC.Coding.BDL26RXErrorPullback.snapshot_output_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:09:16.471597+00:00
-- url     : https://prove2.me/theorems/ce07f05a-3dd8-4a79-9353-391f353b98d9
-- title:
--   BDL26 RXError Pullback: snapshot output eq
-- statement:
--   Identify the unique actual stopped-history snapshot with the same RX selector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXErrorPullback.lean#L301-L306
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXErrorPullback.lean#L301-L306

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

theorem QEC.Coding.BDL26RXErrorPullback.snapshot_output_eq (h : (LevelTwoHistory.physicalStep k).val % 2 = 0) :
    BDL26CanonicalHistoryMarks.outputAt S n sigma k =
      BDL26RXDecoderAdapter.rxStepOutput S (n + 2) (LevelTwoHistory.physicalStep k) h
        (BDL26CanonicalHistoryMarks.inputAt S n sigma k.succ) := by sorry
