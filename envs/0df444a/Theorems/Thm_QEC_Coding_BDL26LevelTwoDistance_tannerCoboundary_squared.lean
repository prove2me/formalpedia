-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_tannerCoboundary_squared
-- name    : QEC.Coding.BDL26LevelTwoDistance.tannerCoboundary_squared
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:27:36.888775+00:00
-- url     : https://prove2.me/theorems/b15c5a9a-d312-456c-87e7-7579f6d28cdf
-- title:
--   BDL26 Level Two Distance: tanner Coboundary squared
-- statement:
--   The actual presentation incidence coboundaries square to zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L638-L654
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L638-L654

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

theorem QEC.Coding.BDL26LevelTwoDistance.tannerCoboundary_squared (P : TannerSquarePresentation) :
    (tannerCoboundary1 P).comp (tannerCoboundary0 P) = 0 := by sorry
