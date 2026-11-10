-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXCohomology_inverse_gauge_class
-- name    : QEC.Coding.BDL26RXCohomology.inverse_gauge_class
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:15:05.051159+00:00
-- url     : https://prove2.me/theorems/4ed9a1d8-e47a-4ea9-ad0f-452f79a426f7
-- title:
--   BDL26 RXCohomology: inverse gauge class
-- statement:
--   Every complete normalization determines the inverse class.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCohomology/Equivalence.lean#L212-L220
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCohomology/Equivalence.lean#L212-L220

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Geometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Equivalence
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXCohomology
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementCochainMaps BDL26RXDecoderAdapter BDL26ReplacementSupport
open BDL26RZMap1CoordinateBridge
open MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXCohomology.inverse_gauge_class (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale)
    (w : Cocycle (rxReplacementPresentation P S)) (v : Cocycle P)
    (f : Word Field (RX0 P S))
    (hf : rxMap1Coord P S v.1 = coordinateWord P S w.1 - rxCoboundary0 P S f) :
    (equiv P A R S).symm (classOf (rxReplacementPresentation P S) w) = classOf P v := by sorry
