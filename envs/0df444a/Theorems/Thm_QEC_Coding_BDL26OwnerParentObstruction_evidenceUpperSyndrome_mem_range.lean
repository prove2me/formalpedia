-- Prove2me | Theorems.Thm_QEC_Coding_BDL26OwnerParentObstruction_evidenceUpperSyndrome_mem_range
-- name    : QEC.Coding.BDL26OwnerParentObstruction.evidenceUpperSyndrome_mem_range
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T04:54:36.047506+00:00
-- url     : https://prove2.me/theorems/a1eae762-f0a6-4957-b3f4-e16c85e9065d
-- title:
--   BDL26 Owner Parent Obstruction: evidence Upper Syndrome mem range
-- statement:
--   The next image is a genuine upper coboundary by the proved cochain relation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerParentObstruction.lean#L325-L331
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerParentObstruction.lean#L325-L331

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalRadialParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementCochainMaps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerParentObstruction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OwnerParentObstruction
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26ReplacementSupport
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps MultiscaleDecoder
open scoped Classical
open BDL26XLocalRadialParity BDL26XLocalConnectingWeight
open scoped BigOperators

theorem QEC.Coding.BDL26OwnerParentObstruction.evidenceUpperSyndrome_mem_range :
    evidenceUpperSyndrome ∈ LinearMap.range
      (rzCoboundary1 (rxReplacementPresentation evidenceStateTwo.presentation scaleFive)
        (rxState scaleFive evidenceStateTwo).admissible scaleFive) := by sorry
