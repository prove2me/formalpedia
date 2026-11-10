-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_xCylinder_coboundary_eq_cocycle
-- name    : QEC.Coding.BDL26LevelTwoDistance.xCylinder_coboundary_eq_cocycle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:37:56.976232+00:00
-- url     : https://prove2.me/theorems/089f235b-5015-48e7-81cf-2ab201977e34
-- title:
--   BDL26 Level Two Distance: x Cylinder coboundary eq cocycle
-- statement:
--   The already proved zero local cohomology coordinate implies actual
--   coboundary/cocycle equality; a quotient class is zero exactly when its word
--   lies in the concrete coboundary submodule.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L576-L588
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L576-L588

import Definitions.Def_QEC_Coding_Core_Duality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXSeedSmallSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoCode
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_AlternatingCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoDistance
open scoped BigOperators
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps BDL26LevelTwoCode
attribute [local instance] QEC.Coding.BDL26LevelTwoDistance.rzQDecidableEq
open BDL26DecodingGraph

theorem QEC.Coding.BDL26LevelTwoDistance.xCylinder_coboundary_eq_cocycle (P : TannerSquarePresentation)
    (A3 : TannerSquareAdmissibleV3 P) (R : TannerSquareCellularRegular P)
    (x : P.X) (S : OddScale) :
    (rxCx P x S).firstCoboundaryCheckCode.carrier =
      (rxCx P x S).middleCocycleCode.carrier := by sorry
