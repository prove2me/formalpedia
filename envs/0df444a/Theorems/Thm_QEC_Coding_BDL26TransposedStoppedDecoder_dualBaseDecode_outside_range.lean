-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_dualBaseDecode_outside_range
-- name    : QEC.Coding.BDL26TransposedStoppedDecoder.dualBaseDecode_outside_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T14:40:19.404416+00:00
-- url     : https://prove2.me/theorems/1b1e694d-dd63-422f-8edb-c2195e4a6d4a
-- title:
--   BDL26 Transposed Stopped Decoder: dual Base Decode outside range
-- statement:
--   Off the exact represented image, both searches fail and the original zero default remains.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/Base.lean#L105-L117
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/Base.lean#L105-L117

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

theorem QEC.Coding.BDL26TransposedStoppedDecoder.dualBaseDecode_outside_range (S : OddScale)
    (sigma : Word BDL26Field (dualPresentation S 2).Z)
    (h : sigma ∉ LinearMap.range (tannerCoboundary1 (dualPresentation S 2))) :
    dualBaseDecode S sigma = 0 := by sorry
