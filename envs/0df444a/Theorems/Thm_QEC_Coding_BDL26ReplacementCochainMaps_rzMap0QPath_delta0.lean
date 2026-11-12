-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_rzMap0QPath_delta0
-- name    : QEC.Coding.BDL26ReplacementCochainMaps.rzMap0QPath_delta0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:05:34.473108+00:00
-- url     : https://prove2.me/theorems/c46e93d0-7f73-4092-990c-47a057622320
-- title:
--   BDL26 Replacement Cochain Maps: rz Map0 QPath delta0
-- statement:
--   The embedded copy-zero X-to-Q path has the fixed #838 Q root and the
--   retained old-X endpoint as its Q boundary, plus the pushed path in every
--   adjacent Z-cylinder.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L752-L773
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L752-L773

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

theorem QEC.Coding.BDL26ReplacementCochainMaps.rzMap0QPath_delta0
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (q : P.Q) (hxq : P.xq x q = true) :
    rzCoboundary0 P A4 S
        (extendRZQEdgeWord P S q (rzMap0QPath P A4 S x q hxq)) =
      canonicalBasisWord
          (Sum.inr ⟨q, rzMap1QRoot P q S⟩ : RZQ P S) +
        canonicalBasisWord
          (Sum.inr ⟨q, rzXQVertex P q x hxq S 0⟩ : RZQ P S) +
        ∑ z : P.Z, if hqz : P.qz q z = true then
          extendRZLocalEdgeWord P S z
            (rzQZDegreeZero P A4.toTannerSquareAdmissible q z hqz S
              (rzMap0QPath P A4 S x q hxq))
        else 0 := by sorry
