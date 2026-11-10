-- Prove2me | Theorems.Thm_QEC_Coding_BDL26OwnerParentObstruction_not_rz_after_rx_degree_one_parent_fibres
-- name    : QEC.Coding.BDL26OwnerParentObstruction.not_rz_after_rx_degree_one_parent_fibres
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T04:53:12.894207+00:00
-- url     : https://prove2.me/theorems/05d3f209-0ac9-484d-b11c-7abe58c52c8a
-- title:
--   BDL26 Owner Parent Obstruction: not rz after rx degree one parent fibres
-- statement:
--   Thus the proposed universal parent-fibre condition on the degree-one
--   basis images is false for any actual RX local edge.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerParentObstruction.lean#L83-L104
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerParentObstruction.lean#L83-L104

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalRadialParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementCochainMaps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerParentObstruction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OwnerParentObstruction
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26ReplacementSupport
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26OwnerParentObstruction.not_rz_after_rx_degree_one_parent_fibres
    (P : TannerSquarePresentation) (S : OddScale)
    (A : TannerSquareAdmissibleV4 (rxReplacementPresentation P S))
    (x : P.X) (edge : DoubleCylinderEdge P x S) :
    ¬ (∀ (source : (rxReplacementPresentation P S).Q)
      (target : RZQ (rxReplacementPresentation P S) S),
      map1Coord (rxReplacementPresentation P S) A S
        (canonicalBasisWord source) target ≠ 0 →
      rxParent P S (rzCorrectionOwner (rxReplacementPresentation P S) S target) =
        some (rxCorrectionOwner P S source)) := by sorry
