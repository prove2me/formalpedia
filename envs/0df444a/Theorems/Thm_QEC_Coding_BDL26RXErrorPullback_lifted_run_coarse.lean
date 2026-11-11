-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXErrorPullback_lifted_run_coarse
-- name    : QEC.Coding.BDL26RXErrorPullback.lifted_run_coarse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:54:52.068734+00:00
-- url     : https://prove2.me/theorems/94000d6e-1ff8-46a5-a9a7-c41a0c51a952
-- title:
--   BDL26 RXError Pullback: lifted run coarse
-- statement:
--   A genuine lifted error realizes the entire prescribed coarse syndrome.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXErrorPullback.lean#L282-L286
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXErrorPullback.lean#L282-L286

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

theorem QEC.Coding.BDL26RXErrorPullback.lifted_run_coarse (h : i.val % 2 = 0) (a : Lower S depth i) :
    (run S depth i h (liftError S depth i a)).coarse.val =
      (indexedFamily S depth).coboundary1 i.castSucc a := by sorry
