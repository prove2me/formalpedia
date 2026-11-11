-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_dualBaseDecode_syndrome
-- name    : QEC.Coding.BDL26TransposedStoppedDecoder.dualBaseDecode_syndrome
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T14:37:33.858315+00:00
-- url     : https://prove2.me/theorems/17cefc1f-3500-4e15-a701-b380de30ea2d
-- title:
--   BDL26 Transposed Stopped Decoder: dual Base Decode syndrome
-- statement:
--   The BDL26 Transposed Stopped Decoder construction uses the dual Base Decode syndrome property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/Base.lean#L50-L55
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/Base.lean#L50-L55

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

theorem QEC.Coding.BDL26TransposedStoppedDecoder.dualBaseDecode_syndrome (S : OddScale)
    (sigma : Word BDL26Field (dualPresentation S 2).Z)
    (h : sigma ∈ LinearMap.range (tannerCoboundary1 (dualPresentation S 2))) :
    tannerCoboundary1 (dualPresentation S 2) (dualBaseDecode S sigma) = sigma := by sorry
