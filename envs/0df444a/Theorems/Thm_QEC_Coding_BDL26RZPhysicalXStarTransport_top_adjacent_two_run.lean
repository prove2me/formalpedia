-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_top_adjacent_two_run
-- name    : QEC.Coding.BDL26RZPhysicalXStarTransport.top_adjacent_two_run
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T17:18:04.906583+00:00
-- url     : https://prove2.me/theorems/c326f731-23a2-4a78-94d9-2ba0c8bbfd03
-- title:
--   BDL26 RZPhysical XStar Transport: top adjacent two run
-- statement:
--   Mandatory adjacent endpoint: p is internally constructed, and both snapshots are the actual histories.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L912-L938
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L912-L938

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

theorem QEC.Coding.BDL26RZPhysicalXStarTransport.top_adjacent_two_run (S : OddScale) (j : Nat) (u : FamilyX S (2*j+4) (topStep j).succ)
    (a b : Upper S (2*j+4) (topStep j))
    (he : Localized S (2*j+4) (topStep j) u a b) :
    ∃ p : Potential S (2*j+4) (topStep j),
      Pullback S (2*j+4) (topStep j) (topStep_odd j)
        (Q0 S (2*j+4) (topStep j) (topStep_odd j) u)
        (Z0 S (2*j+4) (topStep j) (topStep_odd j) u) a b p ∧
      (∀ x : (Old S (2*j+4) (topStep j)).X, ∀ c : BDL26FiniteTannerSquare.Two,
        read0 S (2*j+4) (topStep j) (topStep_odd j) p (.inr (x,c))=0) ∧
      ((indexedDecoderData S (2*j+4)).selectedMap (topStep j)).map1
        (((indexedDecoderData S (2*j+4)).selectedMap (rxStep j)).map1 (secondLower S j u a b))=
        a+b+(topOutput S j a).correction+(topOutput S j b).correction+
        ((indexedDecoderData S (2*j+4)).selectedMap (topStep j)).map1
          ((nextOutput S j a).correction+(nextOutput S j b).correction)+
        (indexedFamily S (2*j+4)).coboundary0 (topStep j).succ (composedPotential S j u a b p) ∧
      (indexedFamily S (2*j+4)).coboundary1 (rxStep j).castSucc (secondLower S j u a b)=
        (nextOutput S j a).coarse.val+(nextOutput S j b).coarse.val ∧
      HammingWeight (secondLower S j u a b) ≤ 7 ∧
      nextOutput S j a=BDL26CanonicalHistoryMarks.outputAt S (2*j+2)
        (errorSyndrome S (2*j+4) (topStep j) a) (nextSnapshotIndex j) ∧
      nextOutput S j b=BDL26CanonicalHistoryMarks.outputAt S (2*j+2)
        (errorSyndrome S (2*j+4) (topStep j) b) (nextSnapshotIndex j) := by sorry
