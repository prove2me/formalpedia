-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_rzOldX_delta0
-- name    : QEC.Coding.BDL26ReplacementCochainMaps.rzOldX_delta0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:19:21.758429+00:00
-- url     : https://prove2.me/theorems/ea26e382-87de-4bf8-a6d5-b7add9b1e9db
-- title:
--   BDL26 Replacement Cochain Maps: rz Old X delta0
-- statement:
--   Coboundary of the retained old-X copy, as the explicit sum of its local
--   terminal coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L1454-L1513
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L1454-L1513

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

theorem QEC.Coding.BDL26ReplacementCochainMaps.rzOldX_delta0
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : P.X) (copy : Two) :
    rzCoboundary0 P A4 S
        (canonicalBasisWord (Sum.inr (x, copy) : RZX P S)) =
      ∑ q : P.Q, if hxq : P.xq x q = true then
        canonicalBasisWord
          (Sum.inr ⟨q, rzXQVertex P q x hxq S copy⟩ : RZQ P S)
      else 0 := by sorry
