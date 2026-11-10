-- Prove2me | Theorems.Thm_QEC_Coding_BDL26OwnerParentObstruction_not_rz_after_rx_degree_two_parent_fibres
-- name    : QEC.Coding.BDL26OwnerParentObstruction.not_rz_after_rx_degree_two_parent_fibres
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:16:56.45919+00:00
-- url     : https://prove2.me/theorems/ef1ec61b-646b-46d4-a1d1-4aa548750ac0
-- title:
--   BDL26 Owner Parent Obstruction: not rz after rx degree two parent fibres
-- statement:
--   In particular, the degree-two target-parent-fibre condition is false.
--   This is a basis-level obstruction, before any decoder or history restriction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerParentObstruction.lean#L108-L129
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerParentObstruction.lean#L108-L129

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

theorem QEC.Coding.BDL26OwnerParentObstruction.not_rz_after_rx_degree_two_parent_fibres
    (P : TannerSquarePresentation) (S : OddScale)
    (A : TannerSquareAdmissibleV4 (rxReplacementPresentation P S))
    (x : P.X) (face : DoubleCylinderFace P x S) :
    ¬ (∀ (source : (rxReplacementPresentation P S).Z)
      (target : RZZ (rxReplacementPresentation P S) S),
      map2Coord (rxReplacementPresentation P S) A S
        (canonicalBasisWord source) target ≠ 0 →
      rxParent P S (.z (rzSyndromeOwner (rxReplacementPresentation P S) S target)) =
        some (rxSyndromeOwner P S source)) := by sorry
