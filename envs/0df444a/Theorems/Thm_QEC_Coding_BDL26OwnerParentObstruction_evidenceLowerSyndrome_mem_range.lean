-- Prove2me | Theorems.Thm_QEC_Coding_BDL26OwnerParentObstruction_evidenceLowerSyndrome_mem_range
-- name    : QEC.Coding.BDL26OwnerParentObstruction.evidenceLowerSyndrome_mem_range
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T04:53:58.749852+00:00
-- url     : https://prove2.me/theorems/8a4c059d-4d1e-49dc-9a37-02451a094bf3
-- title:
--   BDL26 Owner Parent Obstruction: evidence Lower Syndrome mem range
-- statement:
--   The input is a genuine coboundary, not an arbitrary basis cochain.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerParentObstruction.lean#L284-L287
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerParentObstruction.lean#L284-L287

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

theorem QEC.Coding.BDL26OwnerParentObstruction.evidenceLowerSyndrome_mem_range :
    evidenceLowerSyndrome ∈ LinearMap.range
      (tannerCoboundary1 (rxReplacementPresentation evidenceStateTwo.presentation scaleFive)) := by sorry
