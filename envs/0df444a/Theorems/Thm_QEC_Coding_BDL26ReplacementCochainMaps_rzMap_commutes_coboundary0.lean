-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_rzMap_commutes_coboundary0
-- name    : QEC.Coding.BDL26ReplacementCochainMaps.rzMap_commutes_coboundary0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:15:20.866639+00:00
-- url     : https://prove2.me/theorems/0b6e037d-e220-4cb2-932d-a9ee7395faed
-- title:
--   BDL26 Replacement Cochain Maps: rz Map commutes coboundary0
-- statement:
--   The explicit RZ degree-zero/one maps commute with the actual successor
--   coboundary on all finite words.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L1829-L1838
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L1829-L1838

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

theorem QEC.Coding.BDL26ReplacementCochainMaps.rzMap_commutes_coboundary0
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) :
    (rzCoboundary0 P A4 S).comp (rzMap0Coord P S) =
      (map1Coord P A4 S).comp (tannerCoboundary0 P) := by sorry
