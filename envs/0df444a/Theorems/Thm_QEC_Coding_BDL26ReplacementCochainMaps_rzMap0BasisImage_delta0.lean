-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_rzMap0BasisImage_delta0
-- name    : QEC.Coding.BDL26ReplacementCochainMaps.rzMap0BasisImage_delta0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:40:55.363867+00:00
-- url     : https://prove2.me/theorems/7ce612df-e518-4b27-ab54-30a1fa33321e
-- title:
--   BDL26 Replacement Cochain Maps: rz Map0 Basis Image delta0
-- statement:
--   Explicit degree-zero construction commutes on every old-X basis vector.
--   The old terminal and outer-arm terms occur twice and cancel in the binary field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L1776-L1825
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L1776-L1825

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

theorem QEC.Coding.BDL26ReplacementCochainMaps.rzMap0BasisImage_delta0
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) :
    rzCoboundary0 P A4 S (rzMap0BasisImage P S x) =
      map1Coord P A4 S (tannerCoboundary0 P (canonicalBasisWord x)) := by sorry
