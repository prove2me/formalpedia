-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_dualBaseDecode_local
-- name    : QEC.Coding.BDL26TransposedStoppedDecoder.dualBaseDecode_local
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T14:40:31.481329+00:00
-- url     : https://prove2.me/theorems/61ba0032-d940-49b4-8480-c2b65ff9764a
-- title:
--   BDL26 Transposed Stopped Decoder: dual Base Decode local
-- statement:
--   The BDL26 Transposed Stopped Decoder construction uses the dual Base Decode local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/Base.lean#L57-L60
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/Base.lean#L57-L60

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

theorem QEC.Coding.BDL26TransposedStoppedDecoder.dualBaseDecode_local (S : OddScale)
    (e : Word BDL26Field (dualPresentation S 2).Q) (h : dualBaseLocal S e = true) :
    dualBaseLocal S (dualBaseDecode S (tannerCoboundary1 (dualPresentation S 2) e)) = true := by sorry
