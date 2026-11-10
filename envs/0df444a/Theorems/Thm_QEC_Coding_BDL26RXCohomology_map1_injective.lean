-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXCohomology_map1_injective
-- name    : QEC.Coding.BDL26RXCohomology.map1_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:19:20.829209+00:00
-- url     : https://prove2.me/theorems/56e4d19c-23bc-41e0-89e5-4f372f90e9e8
-- title:
--   BDL26 RXCohomology: map1 injective
-- statement:
--   The literal constant Q lift is injective on complete old words.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCohomology/Geometry.lean#L40-L44
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCohomology/Geometry.lean#L40-L44

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Lifts
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology_Representatives
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Geometry
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXCohomology
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementCochainMaps BDL26RXDecoderAdapter BDL26ReplacementSupport
open BDL26RZMap1CoordinateBridge
open BDL26RXStagedRestriction MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXCohomology.map1_injective (P : TannerSquarePresentation) (S : OddScale) :
    Function.Injective (rxMap1Coord P S) := by sorry
