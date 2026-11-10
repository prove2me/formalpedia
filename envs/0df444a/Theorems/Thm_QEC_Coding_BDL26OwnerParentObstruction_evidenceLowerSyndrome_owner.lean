-- Prove2me | Theorems.Thm_QEC_Coding_BDL26OwnerParentObstruction_evidenceLowerSyndrome_owner
-- name    : QEC.Coding.BDL26OwnerParentObstruction.evidenceLowerSyndrome_owner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:40:39.06464+00:00
-- url     : https://prove2.me/theorems/915f783b-f91b-4747-92ea-668aea43cfc8
-- title:
--   BDL26 Owner Parent Obstruction: evidence Lower Syndrome owner
-- statement:
--   Every lower nonzero syndrome coordinate has the same genuine local owner.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerParentObstruction.lean#L315-L322
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerParentObstruction.lean#L315-L322

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

theorem QEC.Coding.BDL26OwnerParentObstruction.evidenceLowerSyndrome_owner (z : RX2 evidenceStateTwo.presentation scaleFive)
    (hz : evidenceLowerSyndrome z ≠ 0) :
    rxSyndromeOwner evidenceStateTwo.presentation scaleFive z = .x evidenceX := by sorry
