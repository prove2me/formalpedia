-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXCohomology_differential1_eq
-- name    : QEC.Coding.BDL26RXCohomology.differential1_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:28:51.962222+00:00
-- url     : https://prove2.me/theorems/acd638ea-53f1-41e2-b5d2-037bbd163b5f
-- title:
--   BDL26 RXCohomology: differential1 eq
-- statement:
--   The materialized actual RX degree-one differential is the raw matrix map.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCohomology/Geometry.lean#L34-L37
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCohomology/Geometry.lean#L34-L37

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

theorem QEC.Coding.BDL26RXCohomology.differential1_eq (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale) :
    tannerCoboundary1 (rxReplacementPresentation P S) = rxCoboundary1 P S := by sorry
