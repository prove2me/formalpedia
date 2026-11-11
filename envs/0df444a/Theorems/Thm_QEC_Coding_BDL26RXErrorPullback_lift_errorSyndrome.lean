-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXErrorPullback_lift_errorSyndrome
-- name    : QEC.Coding.BDL26RXErrorPullback.lift_errorSyndrome
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:54:49.850387+00:00
-- url     : https://prove2.me/theorems/e054d55f-9a22-4f23-90ee-1519924dfff4
-- title:
--   BDL26 RXError Pullback: lift error Syndrome
-- statement:
--   The lift's actual syndrome is exactly the embedded lower coboundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXErrorPullback.lean#L274-L279
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXErrorPullback.lean#L274-L279

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

theorem QEC.Coding.BDL26RXErrorPullback.lift_errorSyndrome (h : i.val % 2 = 0) (a : Lower S depth i) :
    errorSyndrome S depth i (liftError S depth i a) =
      embeddedSyndrome S depth i h
        ⟨(indexedFamily S depth).coboundary1 i.castSucc a, ⟨a,rfl⟩⟩ := by sorry
