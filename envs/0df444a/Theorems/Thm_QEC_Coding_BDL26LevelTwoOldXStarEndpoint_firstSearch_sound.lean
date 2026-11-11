-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoOldXStarEndpoint_firstSearch_sound
-- name    : QEC.Coding.BDL26LevelTwoOldXStarEndpoint.firstSearch_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T16:49:41.023879+00:00
-- url     : https://prove2.me/theorems/85c62116-0866-4ea6-a586-a71b01c30965
-- title:
--   BDL26 Level Two Old XStar Endpoint: first Search sound
-- statement:
--   Both locality and syndrome of the unchanged decoder follow from the actual branch.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoOldXStarEndpoint.lean#L381-L400
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoOldXStarEndpoint.lean#L381-L400

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoOldXStarEndpoint
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoOldXStarEndpoint
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26ReplacementCochainMaps BDL26LevelTwoCode BDL26LevelTwoDistance
open BDL26LevelTwoDecoder BDL26DecodingGraph
open scoped Classical BigOperators

theorem QEC.Coding.BDL26LevelTwoOldXStarEndpoint.firstSearch_sound (S : OddScale) (s : Word F (C S).Z)
    (w : Word F (ExecutableQ S)) (hs : firstSearch S s=some w) :
    decode S s=toActualError S w ∧ levelTwoLocalError S (decode S s) ∧
      tannerCoboundary1 (C S) (decode S s)=s := by sorry
