-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZErrorPullback_correction_delta
-- name    : QEC.Coding.BDL26RZErrorPullback.correction_delta
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:07:17.69957+00:00
-- url     : https://prove2.me/theorems/bf898c48-c1e2-4c88-87eb-0d619f0f6bd8
-- title:
--   BDL26 RZError Pullback: correction delta
-- statement:
--   The BDL26 RZError Pullback construction uses the correction delta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZErrorPullback.lean#L50-L56
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZErrorPullback.lean#L50-L56

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

theorem QEC.Coding.BDL26RZErrorPullback.correction_delta (h : ¬ i.val % 2 = 0) (a : Upper S depth i) :
    (indexedFamily S depth).coboundary1 i.succ (run S depth i h a).correction =
      (errorSyndrome S depth i a).val +
        ((indexedDecoderData S depth).selectedMap i).map2 (run S depth i h a).coarse.val := by sorry
