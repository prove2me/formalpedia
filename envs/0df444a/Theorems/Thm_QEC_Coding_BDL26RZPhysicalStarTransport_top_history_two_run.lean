-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_top_history_two_run
-- name    : QEC.Coding.BDL26RZPhysicalStarTransport.top_history_two_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:43:12.379005+00:00
-- url     : https://prove2.me/theorems/f69b34f9-597a-4ff9-a74d-6f135d588c42
-- title:
--   BDL26 RZPhysical Star Transport: top history two run
-- statement:
--   All original stopped snapshots at physical depth 2*j+4, with full p and Pullback.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalStarTransport.lean#L551-L577
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalStarTransport.lean#L551-L577

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
import Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_top_history_two_run

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RZPhysicalStarTransport
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26DecodingGraph BDL26IndexedDecoder BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementSupport BDL26ReplacementCochainMaps
open BDL26RZDecoderAdapter BDL26RZErrorPullback MultiscaleDecoder
open RZCoarseGraining RZCoarseGrainingData
open BDL26RZFiniteBlockTransport
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (odd : ¬i.val%2=0)

theorem QEC.Coding.BDL26RZPhysicalStarTransport.top_history_two_run (j : Nat)
    (u : FamilyZ S (2*j+4) (topStep j).succ)
    (a b : Upper S (2*j+4) (topStep j))
    (he : Localized S (2*j+4) (topStep j) u a b) :
    ∃ p : Potential S (2*j+4) (topStep j),
      Pullback S (2*j+4) (topStep j) (topStep_odd j)
        (Q0 S (2*j+4) (topStep j) (topStep_odd j) u)
        {parentZ S (2*j+4) (topStep j) (topStep_odd j) u} a b p ∧
      ((indexedDecoderData S (2*j+4)).selectedMap (topStep j)).map1
        (lowerError S (2*j+4) (topStep j) (topStep_odd j) a b)=
        a+b+(topOutput S j a).correction+(topOutput S j b).correction+
          (indexedFamily S (2*j+4)).coboundary0 (topStep j).succ p ∧
      (indexedFamily S (2*j+4)).coboundary1 (topStep j).castSucc
        (lowerError S (2*j+4) (topStep j) (topStep_odd j) a b)=
        (topOutput S j a).coarse.val+(topOutput S j b).coarse.val ∧
      parent S ((topStep j).val+1) (Vertex.z u)=
        some (Vertex.z (parentZ S (2*j+4) (topStep j) (topStep_odd j) u)) ∧
      HammingWeight (lowerError S (2*j+4) (topStep j) (topStep_odd j) a b) ≤ 7 ∧
      (∀ x : (Old S (2*j+4) (topStep j)).X, ∀ copy : BDL26FiniteTannerSquare.Two,
        read0 S (2*j+4) (topStep j) (topStep_odd j) p (.inr (x,copy))=0) := by sorry
