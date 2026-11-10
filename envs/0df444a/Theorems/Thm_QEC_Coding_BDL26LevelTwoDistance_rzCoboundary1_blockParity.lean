-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_rzCoboundary1_blockParity
-- name    : QEC.Coding.BDL26LevelTwoDistance.rzCoboundary1_blockParity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:38:42.893695+00:00
-- url     : https://prove2.me/theorems/dffd6dac-3b7d-4e09-be61-278b408c1523
-- title:
--   BDL26 Level Two Distance: rz Coboundary1 block Parity
-- statement:
--   Actual Z-block syndrome parity is the old syndrome of physical Q parity.
--   This is a coefficient calculation on the materialized RZ incidence.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L847-L919
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L847-L919

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

theorem QEC.Coding.BDL26LevelTwoDistance.rzCoboundary1_blockParity (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (S : OddScale)
    (word : Word Field (RZQ P S)) (z : P.Z) :
    (∑ vertex : ZDoubleCylinderVertex P z S,
      rzCoboundary1 P A4 S word ⟨z, vertex⟩) =
        tannerCoboundary1 P (rzQParity P S word) z := by sorry
