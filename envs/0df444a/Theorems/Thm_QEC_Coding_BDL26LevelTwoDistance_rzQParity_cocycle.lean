-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_rzQParity_cocycle
-- name    : QEC.Coding.BDL26LevelTwoDistance.rzQParity_cocycle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:27:46.053596+00:00
-- url     : https://prove2.me/theorems/15beda24-5cc9-4fa1-92bd-e481ae5115eb
-- title:
--   BDL26 Level Two Distance: rz QParity cocycle
-- statement:
--   Every actual RZ cocycle projects to an old cocycle.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L922-L929
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L922-L929

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

theorem QEC.Coding.BDL26LevelTwoDistance.rzQParity_cocycle (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (S : OddScale)
    (word : Word Field (RZQ P S)) (hc : rzCoboundary1 P A4 S word = 0) :
    tannerCoboundary1 P (rzQParity P S word) = 0 := by sorry
