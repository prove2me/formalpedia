-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_rxMap_commutes_coboundary1
-- name    : QEC.Coding.BDL26ReplacementCochainMaps.rxMap_commutes_coboundary1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:11:33.219648+00:00
-- url     : https://prove2.me/theorems/1628230c-16fb-4876-9d97-76ea5d50ad7e
-- title:
--   BDL26 Replacement Cochain Maps: rx Map commutes coboundary1
-- statement:
--   The concrete RX map commutes with degree-one coboundaries.  The equality
--   is derived from the canonical-basis theorem above.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L596-L604
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L596-L604

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

theorem QEC.Coding.BDL26ReplacementCochainMaps.rxMap_commutes_coboundary1
    (P : TannerSquarePresentation) (S : OddScale) :
    (rxCoboundary1 P S).comp (rxMap P S).map1 =
      (rxMap P S).map2.comp (tannerCoboundary1 P) := by sorry
