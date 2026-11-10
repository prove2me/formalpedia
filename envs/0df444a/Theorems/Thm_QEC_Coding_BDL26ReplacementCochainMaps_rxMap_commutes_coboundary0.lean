-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_rxMap_commutes_coboundary0
-- name    : QEC.Coding.BDL26ReplacementCochainMaps.rxMap_commutes_coboundary0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:13:07.464934+00:00
-- url     : https://prove2.me/theorems/d54b885e-3363-4044-8cd8-f3f9b11fe9c8
-- title:
--   BDL26 Replacement Cochain Maps: rx Map commutes coboundary0
-- statement:
--   The concrete RX map commutes with degree-zero coboundaries.  The equality
--   is derived from the canonical-basis theorem above.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L583-L592
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L583-L592

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

theorem QEC.Coding.BDL26ReplacementCochainMaps.rxMap_commutes_coboundary0
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) :
    (rxCoboundary0 P S).comp (rxMap P S).map0 =
      (rxMap P S).map1.comp (tannerCoboundary0 P) := by sorry
