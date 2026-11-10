-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxCx_exists_local_weight_le
-- name    : QEC.Coding.BDL26RXLocalReplacement.rxCx_exists_local_weight_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:43:30.630196+00:00
-- url     : https://prove2.me/theorems/f0771e7f-fdd3-47d6-bfcf-0662a409f119
-- title:
--   BDL26 RXLocal Replacement: rx Cx exists local weight le
-- statement:
--   F12 X-local syndrome cleaning: the exact local preimage and its actual
--   summed X-to-Q connecting-map budget are both theorem-derived.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeightCertificates.lean#L191-L222
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeightCertificates.lean#L191-L222

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalRadialParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeightCertificates
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26XLocalGridParity BDL26XLocalWeightParity BDL26XLocalConnectingWeight
open BDL26XLocalRadialParity
open scoped BigOperators

theorem QEC.Coding.BDL26RXLocalReplacement.rxCx_exists_local_weight_le
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (x : P.X) (S : OddScale)
    (syndrome : Word Field (DoubleCylinderFace P x S))
    (hs : syndrome ∈ LinearMap.range (wordLinearMapTranspose (doubleCylinderBoundary2 P x S))) :
    ∃ f : Word Field (DoubleCylinderEdge P x S),
      wordLinearMapTranspose (doubleCylinderBoundary2 P x S) f = syndrome ∧
      connectingWeight P A4.toTannerSquareAdmissibleV2.toTannerSquareAdmissible x S f ≤
        HammingWeight syndrome := by sorry
