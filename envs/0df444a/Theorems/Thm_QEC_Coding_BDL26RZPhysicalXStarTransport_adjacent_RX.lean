-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_adjacent_RX
-- name    : QEC.Coding.BDL26RZPhysicalXStarTransport.adjacent_RX
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T16:31:06.871947+00:00
-- url     : https://prove2.me/theorems/5a5209bf-1bf3-44dc-a9d7-3d6ccfc7cb0e
-- title:
--   BDL26 RZPhysical XStar Transport: adjacent RX
-- statement:
--   The complete RX result, including its raw parent, same-run corrections, full q and seven bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L794-L819
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L794-L819

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RZPhysicalXStarTransport
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26DecodingGraph BDL26IndexedDecoder BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementSupport BDL26LevelTwoDistance
open BDL26ReplacementCochainMaps BDL26RZDecoderAdapter BDL26RZErrorPullback
open BDL26RZFiniteBlockTransport MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (odd : ¬i.val%2=0)

theorem QEC.Coding.BDL26RZPhysicalXStarTransport.adjacent_RX (S : OddScale) (j : Nat) (u : FamilyX S (2*j+4) (topStep j).succ)
    (a b : Upper S (2*j+4) (topStep j))
    (he : Localized S (2*j+4) (topStep j) u a b) :
    parent S ((rxStep j).val+1) (Vertex.x (middleX S j u))=
      some (Vertex.x (BDL26RXPhysicalStarTransport.parentX S (2*j+4) (rxStep j) (rxStep_even j) (middleX S j u))) ∧
    ((indexedDecoderData S (2*j+4)).selectedMap (rxStep j)).map1 (secondLower S j u a b)=
      firstLower S j a b+(nextOutput S j a).correction+(nextOutput S j b).correction+
        (indexedFamily S (2*j+4)).coboundary0 (rxStep j).succ (secondPotential S j u a b) ∧
    (indexedFamily S (2*j+4)).coboundary1 (rxStep j).castSucc (secondLower S j u a b)=
      (nextOutput S j a).coarse.val+(nextOutput S j b).coarse.val ∧
    hammingSupport ((nextOutput S j a).correction+(nextOutput S j b).correction) ⊆
      BDL26RXXStarTransport.star1 S (2*j+4) (rxStep j) (rxStep_even j)
        (BDL26RXPhysicalStarTransport.parentX S (2*j+4) (rxStep j) (rxStep_even j) (middleX S j u)) ∧
    hammingSupport (secondPotential S j u a b) ⊆
      BDL26RXXStarTransport.degreeZeroBlock S (2*j+4) (rxStep j) (rxStep_even j)
        (BDL26RXPhysicalStarTransport.parentX S (2*j+4) (rxStep j) (rxStep_even j) (middleX S j u)) ∧
    hammingSupport (secondLower S j u a b) ⊆ BDL26RXPhysicalStarTransport.physicalXStar
      (state S (rxStep j).val).presentation
        (BDL26RXPhysicalStarTransport.parentX S (2*j+4) (rxStep j) (rxStep_even j) (middleX S j u)) ∧
    HammingWeight (secondLower S j u a b) ≤ 7 := by sorry
