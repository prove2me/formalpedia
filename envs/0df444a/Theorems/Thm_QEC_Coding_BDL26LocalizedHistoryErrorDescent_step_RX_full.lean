-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_step_RX_full
-- name    : QEC.Coding.BDL26LocalizedHistoryErrorDescent.step_RX_full
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T18:20:55.928556+00:00
-- url     : https://prove2.me/theorems/368a6ce0-9a40-478e-8d92-148f02d5c503
-- title:
--   BDL26 Localized History Error Descent: step RX full
-- statement:
--   The complete seven-clause RX theorem at any interior original window.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L730-L761
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L730-L761

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalizedHistoryErrorDescent
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalizedHistoryErrorDescent
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
variable (top : LocalizedWord S n sigma tau (TopIndex n))

theorem QEC.Coding.BDL26LocalizedHistoryErrorDescent.step_RX_full (i : StepIndex n) (h : (Edge n i).val%2=0)
    (u : LocalizedWord S n sigma tau i.succ) :
    parent S ((Edge n i).val+1) (Vertex.x u.center)=some (Vertex.x
      (BDL26RXPhysicalStarTransport.parentX S (n+2) (Edge n i) h u.center)) ∧
    ((Data S n).selectedMap i).map1 (step S n sigma tau i u).lower.word=
      u.word+(show (Data S n).family.Cochain1 i.succ from (originalOutput S n sigma i).correction)+
        (show (Data S n).family.Cochain1 i.succ from (originalOutput S n tau i).correction)+
        (Data S n).family.coboundary0 i.succ (step S n sigma tau i u).potential ∧
    (Data S n).family.coboundary1 i.castSucc (step S n sigma tau i u).lower.word=
      (originalOutput S n sigma i).coarse.val+(originalOutput S n tau i).coarse.val ∧
    hammingSupport ((originalOutput S n sigma i).correction+(originalOutput S n tau i).correction) ⊆
      BDL26RXXStarTransport.star1 S (n+2) (Edge n i) h
        (BDL26RXPhysicalStarTransport.parentX S (n+2) (Edge n i) h u.center) ∧
    hammingSupport (step S n sigma tau i u).potential ⊆
      BDL26RXXStarTransport.degreeZeroBlock S (n+2) (Edge n i) h
        (BDL26RXPhysicalStarTransport.parentX S (n+2) (Edge n i) h u.center) ∧
    hammingSupport (step S n sigma tau i u).lower.word ⊆ star S n i.castSucc
      (step S n sigma tau i u).lower.center ∧
    HammingWeight (step S n sigma tau i u).lower.word≤7 := by sorry
