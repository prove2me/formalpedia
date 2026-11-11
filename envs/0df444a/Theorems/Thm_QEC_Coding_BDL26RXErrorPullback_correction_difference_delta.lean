-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXErrorPullback_correction_difference_delta
-- name    : QEC.Coding.BDL26RXErrorPullback.correction_difference_delta
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:52:45.701204+00:00
-- url     : https://prove2.me/theorems/83e7b85e-4651-4d17-b49d-c6b765d8ca72
-- title:
--   BDL26 RXError Pullback: correction difference delta
-- statement:
--   Bare corrections retain the original syndrome difference.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXErrorPullback.lean#L63-L72
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXErrorPullback.lean#L63-L72

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

theorem QEC.Coding.BDL26RXErrorPullback.correction_difference_delta (h : i.val % 2 = 0) (a b : Upper S depth i) :
    (indexedFamily S depth).coboundary1 i.succ
      ((run S depth i h a).correction + (run S depth i h b).correction) =
    (errorSyndrome S depth i a).val + (errorSyndrome S depth i b).val +
      ((indexedDecoderData S depth).selectedMap i).map2 (coarseSum S depth i h a b).val := by sorry
