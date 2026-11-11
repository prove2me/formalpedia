-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_composed_equation
-- name    : QEC.Coding.BDL26RZPhysicalXStarTransport.composed_equation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T16:44:25.471843+00:00
-- url     : https://prove2.me/theorems/3e211074-c7a3-4c1e-aa34-d23fad599a7d
-- title:
--   BDL26 RZPhysical XStar Transport: composed equation
-- statement:
--   The composite image keeps full E, both next original corrections and p+FZ.map0(q).
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L835-L876
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L835-L876

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

theorem QEC.Coding.BDL26RZPhysicalXStarTransport.composed_equation (S : OddScale) (j : Nat) (u : FamilyX S (2*j+4) (topStep j).succ)
    (a b : Upper S (2*j+4) (topStep j))
    (he : Localized S (2*j+4) (topStep j) u a b)
    (p : Potential S (2*j+4) (topStep j))
    (hp : Pullback S (2*j+4) (topStep j) (topStep_odd j)
      (Q0 S (2*j+4) (topStep j) (topStep_odd j) u)
      (Z0 S (2*j+4) (topStep j) (topStep_odd j) u) a b p) :
    ((indexedDecoderData S (2*j+4)).selectedMap (topStep j)).map1
      (((indexedDecoderData S (2*j+4)).selectedMap (rxStep j)).map1 (secondLower S j u a b))=
      a+b+(topOutput S j a).correction+(topOutput S j b).correction+
      ((indexedDecoderData S (2*j+4)).selectedMap (topStep j)).map1
        ((nextOutput S j a).correction+(nextOutput S j b).correction)+
      (indexedFamily S (2*j+4)).coboundary0 (topStep j).succ (composedPotential S j u a b p) := by sorry
