-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementSupport_HammingWeight_sigma
-- name    : QEC.Coding.BDL26ReplacementSupport.HammingWeight_sigma
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:35:06.60947+00:00
-- url     : https://prove2.me/theorems/aa44f1df-d538-4ca4-ac79-e64159043841
-- title:
--   BDL26 Replacement Support: Hamming Weight sigma
-- statement:
--   The weight of a dependent disjoint union is the sum of its fiber weights.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementSupport.lean#L260-L268
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementSupport.lean#L260-L268

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

theorem QEC.Coding.BDL26ReplacementSupport.HammingWeight_sigma
    {Label : Type} [Fintype Label] {Coordinate : Label → Type}
    [∀ label, Fintype (Coordinate label)]
    (word : Word Field (Sigma Coordinate)) :
    HammingWeight word = ∑ label : Label,
      HammingWeight (fun coordinate : Coordinate label => word ⟨label, coordinate⟩) := by sorry
