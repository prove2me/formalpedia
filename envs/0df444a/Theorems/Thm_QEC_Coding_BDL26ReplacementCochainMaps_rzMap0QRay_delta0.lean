-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_rzMap0QRay_delta0
-- name    : QEC.Coding.BDL26ReplacementCochainMaps.rzMap0QRay_delta0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:39:10.052774+00:00
-- url     : https://prove2.me/theorems/fb2bb1de-1cc5-430e-b4f1-4a9550cea7ff
-- title:
--   BDL26 Replacement Cochain Maps: rz Map0 QRay delta0
-- statement:
--   The total successor boundary of the explicit copied arm.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L1030-L1046
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L1030-L1046

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

theorem QEC.Coding.BDL26ReplacementCochainMaps.rzMap0QRay_delta0
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (q : P.Q) (hxq : P.xq x q = true) :
    rzCoboundary0 P A4 S (extendRZQEdgeWord P S q (rzMap0QRay P S x q hxq)) =
      canonicalBasisWord
          (Sum.inr ⟨q, rzMap1QRoot P q S⟩ : RZQ P S) +
        canonicalBasisWord
          (Sum.inr ⟨q, rzXQVertex P q x hxq S 0⟩ : RZQ P S) +
        ∑ z : P.Z, if hqz : P.qz q z = true then
          extendRZLocalEdgeWord P S z
            (rzQZDegreeZero P A4.toTannerSquareAdmissible q z hqz S
              (rzMap0QRay P S x q hxq))
        else 0 := by sorry
