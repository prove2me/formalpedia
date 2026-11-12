-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoCode_levelTwo_graph_index
-- name    : QEC.Coding.BDL26LevelTwoCode.levelTwo_graph_index
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T04:24:41.488627+00:00
-- url     : https://prove2.me/theorems/0df41ec6-b83a-4c4e-ac61-db864a94c893
-- title:
--   BDL26 Level Two Code: level Two graph index
-- statement:
--   The shared graph API has a singleton index zero, hence C_2 is graph index 3.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoCode.lean#L233-L234
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoCode.lean#L233-L234

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoCode
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoCode
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26DecodingGraph BDL26QuantitativeBounds
open scoped BigOperators

theorem QEC.Coding.BDL26LevelTwoCode.levelTwo_graph_index (S : OddScale) :
    level S 3 = tannerLevel (levelTwoPresentation S) := by sorry
