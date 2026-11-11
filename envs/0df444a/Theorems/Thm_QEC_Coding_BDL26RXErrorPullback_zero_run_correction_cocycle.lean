-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXErrorPullback_zero_run_correction_cocycle
-- name    : QEC.Coding.BDL26RXErrorPullback.zero_run_correction_cocycle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:56:27.240125+00:00
-- url     : https://prove2.me/theorems/3bee506f-9713-4fc1-8f28-29e6d63f8ef9
-- title:
--   BDL26 RXError Pullback: zero run correction cocycle
-- statement:
--   Even a non-normalized zero-run correction is an actual cocycle.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXErrorPullback.lean#L251-L254
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXErrorPullback.lean#L251-L254

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

theorem QEC.Coding.BDL26RXErrorPullback.zero_run_correction_cocycle (h : i.val % 2 = 0) :
    (indexedFamily S depth).coboundary1 i.succ (run S depth i h 0).correction = 0 := by sorry
