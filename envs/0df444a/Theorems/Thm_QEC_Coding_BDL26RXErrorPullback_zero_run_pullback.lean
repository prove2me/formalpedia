-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXErrorPullback_zero_run_pullback
-- name    : QEC.Coding.BDL26RXErrorPullback.zero_run_pullback
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T10:00:32.087387+00:00
-- url     : https://prove2.me/theorems/a4995072-6ce4-4ef5-8bcb-490f28610364
-- title:
--   BDL26 RXError Pullback: zero run pullback
-- statement:
--   Direct zero-input pullback does not discard its selected correction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXErrorPullback.lean#L257-L267
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXErrorPullback.lean#L257-L267

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

theorem QEC.Coding.BDL26RXErrorPullback.zero_run_pullback (above : 2 ≤ i.val) (h : i.val % 2 = 0) :
    ∃ (l : Lower S depth i) (p : Potential S depth i),
      ((indexedDecoderData S depth).selectedMap i).map1 l =
        (run S depth i h 0).correction + (indexedFamily S depth).coboundary0 i.succ p ∧
      (indexedFamily S depth).coboundary1 i.castSucc l = 0 ∧
      (indexedFamily S depth).coboundary1 i.succ (run S depth i h 0).correction = 0 ∧
      (indexedFamily S depth).coboundary1 i.succ
        ((indexedFamily S depth).coboundary0 i.succ p) = 0 := by sorry
