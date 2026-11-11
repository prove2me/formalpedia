-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZErrorPullback_correction_difference_delta
-- name    : QEC.Coding.BDL26RZErrorPullback.correction_difference_delta
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:07:44.788254+00:00
-- url     : https://prove2.me/theorems/e7364d1b-a2bb-4134-b211-521c26a61df0
-- title:
--   BDL26 RZError Pullback: correction difference delta
-- statement:
--   Bare corrections retain the original syndrome difference.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZErrorPullback.lean#L59-L68
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZErrorPullback.lean#L59-L68

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

theorem QEC.Coding.BDL26RZErrorPullback.correction_difference_delta (h : ¬ i.val % 2 = 0) (a b : Upper S depth i) :
    (indexedFamily S depth).coboundary1 i.succ
      ((run S depth i h a).correction + (run S depth i h b).correction) =
    (errorSyndrome S depth i a).val + (errorSyndrome S depth i b).val +
      ((indexedDecoderData S depth).selectedMap i).map2 (coarseSum S depth i h a b).val := by sorry
