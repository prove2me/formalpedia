-- Prove2me | Theorems.Thm_QEC_Coding_BDL26OwnerParentObstruction_evidenceLowerSyndrome_nonzero
-- name    : QEC.Coding.BDL26OwnerParentObstruction.evidenceLowerSyndrome_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:40:28.625041+00:00
-- url     : https://prove2.me/theorems/9661d09d-6cdd-4a27-8fb4-2299ce4b08a6
-- title:
--   BDL26 Owner Parent Obstruction: evidence Lower Syndrome nonzero
-- statement:
--   The BDL26 Owner Parent Obstruction construction uses the evidence Lower Syndrome nonzero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerParentObstruction.lean#L289-L312
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerParentObstruction.lean#L289-L312

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

theorem QEC.Coding.BDL26OwnerParentObstruction.evidenceLowerSyndrome_nonzero : evidenceLowerSyndrome ≠ 0 := by sorry
