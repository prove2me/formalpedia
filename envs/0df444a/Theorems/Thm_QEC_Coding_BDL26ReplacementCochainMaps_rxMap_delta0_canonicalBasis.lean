-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_rxMap_delta0_canonicalBasis
-- name    : QEC.Coding.BDL26ReplacementCochainMaps.rxMap_delta0_canonicalBasis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:38:49.031926+00:00
-- url     : https://prove2.me/theorems/dd55c50a-067c-4527-ae45-57857b2942d1
-- title:
--   BDL26 Replacement Cochain Maps: rx Map delta0 canonical Basis
-- statement:
--   Canonical-basis degree-zero commutation for the concrete RX map.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L422-L482
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L422-L482

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

theorem QEC.Coding.BDL26ReplacementCochainMaps.rxMap_delta0_canonicalBasis
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (x : P.X) :
    rxCoboundary0 P S (rxMap0Coord P S (canonicalBasisWord x)) =
      rxMap1Coord P S (tannerCoboundary0 P (canonicalBasisWord x)) := by sorry
