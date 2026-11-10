-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_rxMap_delta1_canonicalBasis
-- name    : QEC.Coding.BDL26ReplacementCochainMaps.rxMap_delta1_canonicalBasis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:38:57.750644+00:00
-- url     : https://prove2.me/theorems/9d34db9c-ffb9-4751-9c9e-5cdf232b342a
-- title:
--   BDL26 Replacement Cochain Maps: rx Map delta1 canonical Basis
-- statement:
--   Canonical-basis degree-one commutation for the concrete RX map.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L487-L552
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L487-L552

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

theorem QEC.Coding.BDL26ReplacementCochainMaps.rxMap_delta1_canonicalBasis
    (P : TannerSquarePresentation) (S : OddScale) (q : P.Q) :
    rxCoboundary1 P S (rxMap1Coord P S (canonicalBasisWord q)) =
      rxMap2Coord P S (tannerCoboundary1 P (canonicalBasisWord q)) := by sorry
