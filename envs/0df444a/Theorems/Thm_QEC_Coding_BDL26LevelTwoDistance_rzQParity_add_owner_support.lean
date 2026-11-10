-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_rzQParity_add_owner_support
-- name    : QEC.Coding.BDL26LevelTwoDistance.rzQParity_add_owner_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:49:43.267993+00:00
-- url     : https://prove2.me/theorems/bc87afd7-be35-44f1-a462-69230804df3a
-- title:
--   BDL26 Level Two Distance: rz QParity add owner support
-- statement:
--   Two independently local physical errors produce Q parity in at most
--   the two selected owner labels, even when the centers differ.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L820-L832
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L820-L832

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

theorem QEC.Coding.BDL26LevelTwoDistance.rzQParity_add_owner_support (P : TannerSquarePresentation) (S : OddScale)
    (first second : Word Field (RZQ P S)) (a b : Vertex P)
    (ha : ∀ c, first c ≠ 0 → BDL26ReplacementSupport.rzCorrectionOwner P S c = a)
    (hb : ∀ c, second c ≠ 0 → BDL26ReplacementSupport.rzCorrectionOwner P S c = b)
    (q : P.Q) (hq : rzQParity P S (first + second) q ≠ 0) :
    Vertex.q q = a ∨ Vertex.q q = b := by sorry
