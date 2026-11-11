-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_dualBaseDecode_xSyndrome
-- name    : QEC.Coding.BDL26TransposedStoppedDecoder.dualBaseDecode_xSyndrome
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T14:45:13.954663+00:00
-- url     : https://prove2.me/theorems/87168d71-4627-4065-9e79-177b4d542767
-- title:
--   BDL26 Transposed Stopped Decoder: dual Base Decode x Syndrome
-- statement:
--   Same-carrier physical right inverse, derived from the actual finite lookup.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/Base.lean#L125-L130
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/Base.lean#L125-L130

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_LocalSteps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Rows
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_Base
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26TransposedStoppedDecoder
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26LevelTwoCode BDL26LevelTwoDecoder BDL26ReplacementSupport
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RXDecoderAdapter
open BDL26RZMap1CoordinateBridge MultiscaleDecoder Coordinates
open scoped Classical

theorem QEC.Coding.BDL26TransposedStoppedDecoder.dualBaseDecode_xSyndrome (S : OddScale)
    (sigma : Word BDL26Field (BDL26CSSHamiltonian.XLabel S 2))
    (h : sigma ∈ LinearMap.range (BDL26CSSHamiltonian.xSyndrome S 2)) :
    BDL26CSSHamiltonian.xSyndrome S 2 (dualBaseDecode S sigma) = sigma := by sorry
