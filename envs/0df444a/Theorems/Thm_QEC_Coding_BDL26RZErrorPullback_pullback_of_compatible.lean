-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZErrorPullback_pullback_of_compatible
-- name    : QEC.Coding.BDL26RZErrorPullback.pullback_of_compatible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:07:37.42466+00:00
-- url     : https://prove2.me/theorems/c5f6b693-56cc-4648-923a-762c74c68dc7
-- title:
--   BDL26 RZError Pullback: pullback of compatible
-- statement:
--   Actual coarse validity and compatibility suffice to construct both full words.
--   This helper's compatibility is derived by the actual-run endpoints below.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZErrorPullback.lean#L154-L195
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZErrorPullback.lean#L154-L195

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

theorem QEC.Coding.BDL26RZErrorPullback.pullback_of_compatible (h : ¬ i.val % 2 = 0) (E : Upper S depth i)
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
