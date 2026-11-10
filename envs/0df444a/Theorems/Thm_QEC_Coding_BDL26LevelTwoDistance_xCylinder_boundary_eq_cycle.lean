-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_xCylinder_boundary_eq_cycle
-- name    : QEC.Coding.BDL26LevelTwoDistance.xCylinder_boundary_eq_cycle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:46:54.00716+00:00
-- url     : https://prove2.me/theorems/6e2a7b4e-e3e1-4486-ada9-87aa335f9b22
-- title:
--   BDL26 Level Two Distance: x Cylinder boundary eq cycle
-- statement:
--   Finite nondegenerate duality turns the actual X-cylinder cohomology
--   calculation into a cellular cycle-filling statement.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L592-L605
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L592-L605

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

theorem QEC.Coding.BDL26LevelTwoDistance.xCylinder_boundary_eq_cycle (P : TannerSquarePresentation)
    (A3 : TannerSquareAdmissibleV3 P) (R : TannerSquareCellularRegular P)
    (x : P.X) (S : OddScale) :
    (rxCx P x S).middleBoundaryCode.carrier =
      (rxCx P x S).middleCycleCode.carrier := by sorry
