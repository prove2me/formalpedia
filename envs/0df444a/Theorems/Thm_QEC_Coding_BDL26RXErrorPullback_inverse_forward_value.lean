-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXErrorPullback_inverse_forward_value
-- name    : QEC.Coding.BDL26RXErrorPullback.inverse_forward_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:53:29.625205+00:00
-- url     : https://prove2.me/theorems/422eda32-1ba5-4d51-90a7-c81d475706b2
-- title:
--   BDL26 RXError Pullback: inverse forward value
-- statement:
--   The actual indexed forward word is literally the selected map1.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXErrorPullback.lean#L137-L141
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXErrorPullback.lean#L137-L141

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

theorem QEC.Coding.BDL26RXErrorPullback.inverse_forward_value (v : Cocycle (state S i.val).presentation) :
    (nextCocycle S i.val (state S i.val) v).val =
      ((indexedDecoderData S depth).selectedMap i).map1 v.val := by sorry
