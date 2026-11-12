-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_levelTwoLocalError_iff_f17
-- name    : QEC.Coding.BDL26LevelTwoDistance.levelTwoLocalError_iff_f17
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T04:25:22.749636+00:00
-- url     : https://prove2.me/theorems/bf50a3bb-ec3f-4873-9456-4a123d80db75
-- title:
--   BDL26 Level Two Distance: level Two Local Error iff f17
-- statement:
--   The physical owner predicate is definitionally the approved abstract
--   F17 predicate for any decoder-data carrier assembled with these coordinates.
--   No decoder correctness or geometric conclusion is assumed or inferred.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L625-L635
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L625-L635

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

theorem QEC.Coding.BDL26LevelTwoDistance.levelTwoLocalError_iff_f17 (S : OddScale) {depth : Nat}
    (hdepth : 2 ≤ depth)
    (D : MultiscaleDecoder.BDL26DecoderData depth
      (fun _ => (levelTwoPresentation S).X)
      (fun _ => (levelTwoPresentation S).Q)
      (fun _ => (levelTwoPresentation S).Z))
    (error : Word Field (levelTwoPresentation S).Q) :
    levelTwoLocalError S error ↔
      MultiscaleDecoder.LevelTwoLocalError
        (V := fun _ => Vertex (levelOnePresentation S)) D hdepth
        (levelTwoLocalComplex S) error := by sorry
