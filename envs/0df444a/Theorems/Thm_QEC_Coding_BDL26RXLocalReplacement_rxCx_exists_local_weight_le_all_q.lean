-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxCx_exists_local_weight_le_all_q
-- name    : QEC.Coding.BDL26RXLocalReplacement.rxCx_exists_local_weight_le_all_q
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:43:30.698281+00:00
-- url     : https://prove2.me/theorems/eac49023-b3d8-48a2-8f50-932b59dc9221
-- title:
--   BDL26 RXLocal Replacement: rx Cx exists local weight le all q
-- statement:
--   F12 stated over every old Q block, with nonincident blocks contributing zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeightCertificates.lean#L225-L259
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeightCertificates.lean#L225-L259

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalRadialParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeightCertificates
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26XLocalGridParity BDL26XLocalWeightParity BDL26XLocalConnectingWeight
open BDL26XLocalRadialParity
open scoped BigOperators

theorem QEC.Coding.BDL26RXLocalReplacement.rxCx_exists_local_weight_le_all_q
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (x : P.X) (S : OddScale)
    (syndrome : Word Field (DoubleCylinderFace P x S))
    (hs : syndrome ∈ LinearMap.range (wordLinearMapTranspose (doubleCylinderBoundary2 P x S))) :
    ∃ f : Word Field (DoubleCylinderEdge P x S),
      wordLinearMapTranspose (doubleCylinderBoundary2 P x S) f = syndrome ∧
      (∑ q : P.Q, if hq : P.xq x q = true then
        HammingWeight (rxXQDegreeOne P
          A4.toTannerSquareAdmissibleV2.toTannerSquareAdmissible q x hq S f) else 0) ≤
        HammingWeight syndrome := by sorry
