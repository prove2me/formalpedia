-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_topOutput_coarse
-- name    : QEC.Coding.BDL26UniformHistoryObstruction.topOutput_coarse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:33:36.746599+00:00
-- url     : https://prove2.me/theorems/d3aaf56e-a503-4019-83b0-7775cf986c16
-- title:
--   BDL26 Uniform History Obstruction: top Output coarse
-- statement:
--   The BDL26 Uniform History Obstruction construction uses the top Output coarse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformWitness.lean#L182-L187
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformWitness.lean#L182-L187

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformHistoryObstruction
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks
open BDL26OwnerParentObstruction BDL26ReplacementSupport BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps
open BDL26XLocalRadialParity BDL26XLocalConnectingWeight
open MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26UniformHistoryObstruction.topOutput_coarse (S : OddScale) (j : Nat) :
    (topOutput S j).coarse = lowerSyndrome S j := by sorry
