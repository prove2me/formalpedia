-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoCode_levelTwo_correctionRegion_mem
-- name    : QEC.Coding.BDL26LevelTwoCode.levelTwo_correctionRegion_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T04:25:41.769099+00:00
-- url     : https://prove2.me/theorems/01fed47c-4426-4756-89ef-144d377afd24
-- title:
--   BDL26 Level Two Code: level Two correction Region mem
-- statement:
--   The stopping code's local correction regions are exactly its Tanner stars.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoCode.lean#L237-L241
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoCode.lean#L237-L241

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoCode
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoCode
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26DecodingGraph BDL26QuantitativeBounds
open scoped BigOperators

theorem QEC.Coding.BDL26LevelTwoCode.levelTwo_correctionRegion_mem (S : OddScale)
    (u v : Vertex (levelTwoPresentation S)) :
    u ∈ (correctionRegion S 2 v).vertices ↔
      u = v ∨ tannerDirected (levelTwoPresentation S) u v = true := by sorry
