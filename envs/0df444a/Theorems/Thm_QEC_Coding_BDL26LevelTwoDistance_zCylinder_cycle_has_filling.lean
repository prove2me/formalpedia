-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_zCylinder_cycle_has_filling
-- name    : QEC.Coding.BDL26LevelTwoDistance.zCylinder_cycle_has_filling
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:27:58.123299+00:00
-- url     : https://prove2.me/theorems/edbd5d2d-ac44-4902-b567-65b9b8972e61
-- title:
--   BDL26 Level Two Distance: z Cylinder cycle has filling
-- statement:
--   Every zero-boundary Z-cylinder edge chain has a genuine face filling.
--   This is the local exactness used after removing Q-block parities.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L609-L620
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L609-L620

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

theorem QEC.Coding.BDL26LevelTwoDistance.zCylinder_cycle_has_filling (P : TannerSquarePresentation)
    (A3 : TannerSquareAdmissibleV3 P) (R : TannerSquareCellularRegular P)
    (z : P.Z) (S : OddScale) (word : Word Field (ZDoubleCylinderEdge P z S))
    (hword : doubleCylinderBoundary1 (transposePresentation P) z S word = 0) :
    ∃ faces : Word Field (ZDoubleCylinderFace P z S),
      doubleCylinderBoundary2 (transposePresentation P) z S faces = word := by sorry
