-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXErrorPullback_zero_run_coarse
-- name    : QEC.Coding.BDL26RXErrorPullback.zero_run_coarse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:36:01.052769+00:00
-- url     : https://prove2.me/theorems/26b7c933-f6f2-47fc-a925-b866ad786470
-- title:
--   BDL26 RXError Pullback: zero run coarse
-- statement:
--   The coarse zero word follows from the actual RX factor-two inequality.
--   The actual correction at zero is retained, not assumed to vanish.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXErrorPullback.lean#L242-L248
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXErrorPullback.lean#L242-L248

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

theorem QEC.Coding.BDL26RXErrorPullback.zero_run_coarse (h : i.val % 2 = 0) : (run S depth i h 0).coarse.val = 0 := by sorry
