-- Prove2me | Theorems.Thm_QEC_Coding_BDL26OwnerParentObstruction_rzMap2_apply
-- name    : QEC.Coding.BDL26OwnerParentObstruction.rzMap2_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:23:23.432995+00:00
-- url     : https://prove2.me/theorems/9620a8dd-c72c-48ee-9259-b50edce537d6
-- title:
--   BDL26 Owner Parent Obstruction: rz Map2 apply
-- statement:
--   Arbitrary-word RZ evaluation, retaining the actual root and owner.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerParentObstruction.lean#L240-L252
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerParentObstruction.lean#L240-L252

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

theorem QEC.Coding.BDL26OwnerParentObstruction.rzMap2_apply (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (S : OddScale) (s : Word BDL26Field P.Z) (z : P.Z)
    (v : ZDoubleCylinderVertex P z S) :
    map2Coord P A S s ⟨z,v⟩ = if v = rzMap1ZRoot P A z S then s z else 0 := by sorry
