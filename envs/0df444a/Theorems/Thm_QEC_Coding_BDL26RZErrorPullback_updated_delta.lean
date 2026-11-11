-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZErrorPullback_updated_delta
-- name    : QEC.Coding.BDL26RZErrorPullback.updated_delta
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:07:29.248008+00:00
-- url     : https://prove2.me/theorems/bb758ad6-cf9a-44fe-aeb4-6de14b451039
-- title:
--   BDL26 RZError Pullback: updated delta
-- statement:
--   The full updated-error difference has precisely the transported coarse syndrome.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZErrorPullback.lean#L71-L84
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZErrorPullback.lean#L71-L84

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

theorem QEC.Coding.BDL26RZErrorPullback.updated_delta (h : ¬ i.val % 2 = 0) (a b : Upper S depth i) :
    (indexedFamily S depth).coboundary1 i.succ (updated S depth i h a b) =
      ((indexedDecoderData S depth).selectedMap i).map2 (coarseSum S depth i h a b).val := by sorry
