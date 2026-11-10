-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_rzMap_commutes_coboundary1
-- name    : QEC.Coding.BDL26ReplacementCochainMaps.rzMap_commutes_coboundary1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:12:48.796516+00:00
-- url     : https://prove2.me/theorems/a9de22e9-075d-4f29-a780-f81b017e7168
-- title:
--   BDL26 Replacement Cochain Maps: rz Map commutes coboundary1
-- statement:
--   Existing #838 degree-one basis commutation, promoted to all finite words
--   by canonical-basis extensionality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L1863-L1874
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L1863-L1874

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCoordinateBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementCochainMaps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementCochainMaps
open scoped BigOperators Classical
open QEC.Coding
open QEC.Coding.BDL26FiniteTannerSquare
open QEC.Coding.BDL26TannerLocalRegularity
open QEC.Coding.BDL26RXLocalReplacement
open QEC.Coding.BDL26RZLocalReplacement
open QEC.Coding.BDL26RZMap1CoordinateBridge
open QEC.Coding.MultiscaleDecoder

theorem QEC.Coding.BDL26ReplacementCochainMaps.rzMap_commutes_coboundary1
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) :
    (rzCoboundary1 P A4 S).comp (map1Coord P A4 S) =
      (map2Coord P A4 S).comp (tannerCoboundary1 P) := by sorry
