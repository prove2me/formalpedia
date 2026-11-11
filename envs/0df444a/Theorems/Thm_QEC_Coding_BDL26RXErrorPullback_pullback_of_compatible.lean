-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXErrorPullback_pullback_of_compatible
-- name    : QEC.Coding.BDL26RXErrorPullback.pullback_of_compatible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:04:43.611396+00:00
-- url     : https://prove2.me/theorems/f741e727-78db-45eb-a7d0-fc9c712f5f79
-- title:
--   BDL26 RXError Pullback: pullback of compatible
-- statement:
--   Actual coarse validity and compatibility suffice to construct both full words.
--   This helper's compatibility is derived by the actual-run endpoints below.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXErrorPullback.lean#L168-L209
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXErrorPullback.lean#L168-L209

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

theorem QEC.Coding.BDL26RXErrorPullback.pullback_of_compatible (h : i.val % 2 = 0) (E : Upper S depth i)
    (tau : (indexedFamily S depth).Syndrome i.castSucc)
    (hE : (indexedFamily S depth).coboundary1 i.succ E =
      ((indexedDecoderData S depth).selectedMap i).map2 tau.val) :
    ∃ (l : Lower S depth i) (p : Potential S depth i),
      ((indexedDecoderData S depth).selectedMap i).map1 l =
        E + (indexedFamily S depth).coboundary0 i.succ p ∧
      (indexedFamily S depth).coboundary1 i.castSucc l = tau.val ∧
      ((indexedDecoderData S depth).selectedMap i).map2 tau.val =
        (indexedFamily S depth).coboundary1 i.succ E ∧
      (indexedFamily S depth).coboundary1 i.succ
        ((indexedFamily S depth).coboundary0 i.succ p) = 0 := by sorry
