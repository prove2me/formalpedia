-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_subdivisionWholeFaceChain_boundary
-- name    : QEC.Coding.BDL26ReplacementCochainMaps.subdivisionWholeFaceChain_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:39:21.671174+00:00
-- url     : https://prove2.me/theorems/a6cc7426-712d-4912-ae2a-e6822f206b2f
-- title:
--   BDL26 Replacement Cochain Maps: subdivision Whole Face Chain boundary
-- statement:
--   Internal grid edges occur twice in the whole-face filling, leaving exactly
--   the four subdivided outer sides.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L1132-L1208
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L1132-L1208

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

theorem QEC.Coding.BDL26ReplacementCochainMaps.subdivisionWholeFaceChain_boundary
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) :
    subdivisionBoundary2 P x S (subdivisionWholeFaceChain P x S face) =
      (∑ i : Fin S.half,
          canonicalBasisWord
            (subdivisionHorizontalEdge P x S face i (rzGridZero S))) +
        (∑ i : Fin S.half,
          canonicalBasisWord
            (subdivisionHorizontalEdge P x S face i (rzGridLast S))) +
        (∑ j : Fin S.half,
          canonicalBasisWord
            (subdivisionVerticalEdge P x S face (rzGridZero S) j)) +
      (∑ j : Fin S.half,
        canonicalBasisWord
          (subdivisionVerticalEdge P x S face (rzGridLast S) j)) := by sorry
