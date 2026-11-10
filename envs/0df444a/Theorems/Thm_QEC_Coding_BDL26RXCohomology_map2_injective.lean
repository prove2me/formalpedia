-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXCohomology_map2_injective
-- name    : QEC.Coding.BDL26RXCohomology.map2_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:17:38.402749+00:00
-- url     : https://prove2.me/theorems/bb32e055-efec-45cf-8516-6cd11aadeec1
-- title:
--   BDL26 RXCohomology: map2 injective
-- statement:
--   The actual old-Z diagonal coordinates make map2 injective.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCohomology/Geometry.lean#L47-L51
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCohomology/Geometry.lean#L47-L51

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

theorem QEC.Coding.BDL26RXCohomology.map2_injective (P : TannerSquarePresentation) (S : OddScale) :
    Function.Injective (rxMap2Coord P S) := by sorry
