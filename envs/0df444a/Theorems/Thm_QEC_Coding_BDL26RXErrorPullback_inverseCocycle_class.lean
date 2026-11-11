-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXErrorPullback_inverseCocycle_class
-- name    : QEC.Coding.BDL26RXErrorPullback.inverseCocycle_class
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:53:47.341394+00:00
-- url     : https://prove2.me/theorems/1d5d324b-97bf-408a-8d58-1f9a7f2b9275
-- title:
--   BDL26 RXError Pullback: inverse Cocycle class
-- statement:
--   Its quotient class is exactly the actual RX H¹ inverse.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXErrorPullback.lean#L107-L114
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXErrorPullback.lean#L107-L114

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Indexed
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXErrorPullback_EmbeddedReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXErrorPullback
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXErrorPullback
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge BDL26RXCohomology BDL26AlternatingCochain
open BDL26RZCohomology (mem_cocycle_iff mem_boundary_iff)
open MultiscaleDecoder BDL26OwnerIncidenceMasks
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)

theorem QEC.Coding.BDL26RXErrorPullback.inverseCocycle_class (h : i.val % 2 = 0)
    (w : Cocycle (state S (i.val + 1)).presentation) :
    classOf (state S i.val).presentation (inverseCocycle S depth i h w) =
      (nextEquiv S i.val (state S i.val) h).symm
        (classOf (state S (i.val + 1)).presentation w) := by sorry
