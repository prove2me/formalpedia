-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementSupport_rzLocalParity_weight_le
-- name    : QEC.Coding.BDL26ReplacementSupport.rzLocalParity_weight_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T00:57:58.144376+00:00
-- url     : https://prove2.me/theorems/a83c8880-6845-4c26-9748-22829c23b2ef
-- title:
--   BDL26 Replacement Support: rz Local Parity weight le
-- statement:
--   Concrete RZ local bound applied to the actual tagged Z cylinder.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementSupport.lean#L160-L166
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementSupport.lean#L160-L166

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCoordinateBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QLocalWeight
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXLocalCleaning
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementSupport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open MultiscaleDecoder
open scoped BigOperators Classical

theorem QEC.Coding.BDL26ReplacementSupport.rzLocalParity_weight_le
    (P : TannerSquarePresentation) (S : OddScale) (z : P.Z)
    (syndrome : Word Field (RZZ P S)) :
    HammingWeight (parityBit (fun vertex : ZDoubleCylinderVertex P z S =>
      syndrome ⟨z, vertex⟩)) ≤
      HammingWeight (fun vertex : ZDoubleCylinderVertex P z S => syndrome ⟨z, vertex⟩) := by sorry
