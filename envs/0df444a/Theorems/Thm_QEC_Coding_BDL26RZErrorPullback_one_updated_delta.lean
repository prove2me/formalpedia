-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZErrorPullback_one_updated_delta
-- name    : QEC.Coding.BDL26RZErrorPullback.one_updated_delta
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:09:23.991472+00:00
-- url     : https://prove2.me/theorems/55074ef5-2567-4315-91a7-67e6a374849b
-- title:
--   BDL26 RZError Pullback: one updated delta
-- statement:
--   The BDL26 RZError Pullback construction uses the one updated delta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZErrorPullback.lean#L86-L91
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZErrorPullback.lean#L86-L91

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

theorem QEC.Coding.BDL26RZErrorPullback.one_updated_delta (h : ¬ i.val % 2 = 0) (a : Upper S depth i) :
    (indexedFamily S depth).coboundary1 i.succ (a + (run S depth i h a).correction) =
      ((indexedDecoderData S depth).selectedMap i).map2 (run S depth i h a).coarse.val := by sorry
