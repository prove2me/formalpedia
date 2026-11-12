-- Prove2me | Theorems.Thm_QEC_Coding_BDL26OwnerParentObstruction_base_scale_five_not_degree_two_parent_fibres
-- name    : QEC.Coding.BDL26OwnerParentObstruction.base_scale_five_not_degree_two_parent_fibres
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T04:53:31.576287+00:00
-- url     : https://prove2.me/theorems/3e660fbc-4953-4b1b-aa5c-86f985336327
-- title:
--   BDL26 Owner Parent Obstruction: base scale five not degree two parent fibres
-- statement:
--   Fully materialized scale-five counterexample, with the successor's proved
--   admissibility rather than an assumed valid replacement.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerParentObstruction.lean#L139-L151
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerParentObstruction.lean#L139-L151

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

theorem QEC.Coding.BDL26OwnerParentObstruction.base_scale_five_not_degree_two_parent_fibres :
    let P := baseTannerSquarePresentation
    let S := scaleFive
    let A := (rxState S baseState).admissible
    ¬ (∀ (source : (rxReplacementPresentation P S).Z)
      (target : RZZ (rxReplacementPresentation P S) S),
      map2Coord (rxReplacementPresentation P S) A S
        (canonicalBasisWord source) target ≠ 0 →
      rxParent P S (.z (rzSyndromeOwner (rxReplacementPresentation P S) S target)) =
        some (rxSyndromeOwner P S source)) := by sorry
