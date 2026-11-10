-- Prove2me | Theorems.Thm_QEC_Coding_BDL26OwnerParentObstruction_extendedRadialGauge_supported
-- name    : QEC.Coding.BDL26OwnerParentObstruction.extendedRadialGauge_supported
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:34:56.031766+00:00
-- url     : https://prove2.me/theorems/fca862bc-26e1-4cad-aee0-e5603266c3c5
-- title:
--   BDL26 Owner Parent Obstruction: extended Radial Gauge supported
-- statement:
--   A radial gauge extended into X creates no syndrome outside that X block.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerParentObstruction.lean#L187-L225
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerParentObstruction.lean#L187-L225

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
open BDL26XLocalRadialParity BDL26XLocalConnectingWeight
open scoped BigOperators

theorem QEC.Coding.BDL26OwnerParentObstruction.extendedRadialGauge_supported (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (x : P.X)
    (selected : Fin 2) (alpha : Neighbor P x → BDL26Field)
    (z : RX2 P S) (hz : rxSyndromeOwner P S z ≠ .x x) :
    wordLinearMapTranspose (rxBoundary2 P S)
      (extendXCorrection P S x (radialGauge P A x S selected alpha)) z = 0 := by sorry
