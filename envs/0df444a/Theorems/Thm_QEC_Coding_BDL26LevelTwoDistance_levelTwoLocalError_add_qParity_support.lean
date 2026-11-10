-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_levelTwoLocalError_add_qParity_support
-- name    : QEC.Coding.BDL26LevelTwoDistance.levelTwoLocalError_add_qParity_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:48:30.7574+00:00
-- url     : https://prove2.me/theorems/4938b793-5ced-42af-bc7c-6b3ef43a136a
-- title:
--   BDL26 Level Two Distance: level Two Local Error add q Parity support
-- statement:
--   The BDL26 Level Two Distance construction uses the level Two Local Error add q Parity support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L834-L843
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L834-L843

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

theorem QEC.Coding.BDL26LevelTwoDistance.levelTwoLocalError_add_qParity_support (S : OddScale)
    (first second : Word Field (levelTwoPresentation S).Q)
    (hfirst : levelTwoLocalError S first) (hsecond : levelTwoLocalError S second) :
    ∃ firstOwner secondOwner : Vertex (levelOnePresentation S),
      ∀ q, rzQParity (levelOnePresentation S) S (first + second) q ≠ 0 →
        Vertex.q q = firstOwner ∨ Vertex.q q = secondOwner := by sorry
