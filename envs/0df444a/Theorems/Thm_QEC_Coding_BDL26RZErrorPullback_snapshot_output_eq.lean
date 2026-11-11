-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZErrorPullback_snapshot_output_eq
-- name    : QEC.Coding.BDL26RZErrorPullback.snapshot_output_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:08:17.166181+00:00
-- url     : https://prove2.me/theorems/2908c001-7f6a-48a8-8de2-ab885e306e5f
-- title:
--   BDL26 RZError Pullback: snapshot output eq
-- statement:
--   Identify the unique actual stopped-history snapshot with the same RZ selector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZErrorPullback.lean#L237-L242
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZErrorPullback.lean#L237-L242

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

theorem QEC.Coding.BDL26RZErrorPullback.snapshot_output_eq (h : ¬ (LevelTwoHistory.physicalStep k).val % 2 = 0) :
    BDL26CanonicalHistoryMarks.outputAt S n sigma k =
      BDL26RZDecoderAdapter.rzStepOutput S (n + 2) (LevelTwoHistory.physicalStep k) h
        (BDL26CanonicalHistoryMarks.inputAt S n sigma k.succ) := by sorry
