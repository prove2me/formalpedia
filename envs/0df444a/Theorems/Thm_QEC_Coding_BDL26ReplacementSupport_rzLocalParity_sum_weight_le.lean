-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementSupport_rzLocalParity_sum_weight_le
-- name    : QEC.Coding.BDL26ReplacementSupport.rzLocalParity_sum_weight_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T00:59:23.187147+00:00
-- url     : https://prove2.me/theorems/7723a865-d7e1-4189-8fb7-c6904a903d62
-- title:
--   BDL26 Replacement Support: rz Local Parity sum weight le
-- statement:
--   All one-bit RZ local coordinates jointly obey the original syndrome budget.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementSupport.lean#L301-L309
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementSupport.lean#L301-L309

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

theorem QEC.Coding.BDL26ReplacementSupport.rzLocalParity_sum_weight_le
    (P : TannerSquarePresentation) (S : OddScale)
    (syndrome : Word Field (RZZ P S)) :
    (∑ z : P.Z, HammingWeight
      (parityBit (fun vertex : ZDoubleCylinderVertex P z S => syndrome ⟨z, vertex⟩))) ≤
      HammingWeight syndrome := by sorry
