-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZErrorPullback_snapshot_entry_eq
-- name    : QEC.Coding.BDL26RZErrorPullback.snapshot_entry_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T10:29:56.731078+00:00
-- url     : https://prove2.me/theorems/ff1d8512-b67b-4b17-8c56-5568cd8bf2ba
-- title:
--   BDL26 RZError Pullback: snapshot entry eq
-- statement:
--   The BDL26 RZError Pullback construction uses the snapshot entry eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZErrorPullback.lean#L244-L250
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZErrorPullback.lean#L244-L250

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

theorem QEC.Coding.BDL26RZErrorPullback.snapshot_entry_eq (h : ¬ (LevelTwoHistory.physicalStep k).val % 2 = 0) :
    BDL26CanonicalHistoryMarks.entryAt S n sigma k.succ =
      CorrectionHistoryEntry.step k
        (LevelTwoHistory.suffixOutput (indexedDecoderData S (n + 2)) k
          (BDL26RZDecoderAdapter.rzStepOutput S (n + 2) (LevelTwoHistory.physicalStep k) h
            (BDL26CanonicalHistoryMarks.inputAt S n sigma k.succ))) := by sorry
