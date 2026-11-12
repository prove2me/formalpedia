-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_dualBaseDecode_first_local
-- name    : QEC.Coding.BDL26TransposedStoppedDecoder.dualBaseDecode_first_local
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T17:20:07.011204+00:00
-- url     : https://prove2.me/theorems/891c0d68-81d1-420f-a9f0-21cb55d7a3a3
-- title:
--   BDL26 Transposed Stopped Decoder: dual Base Decode first local
-- statement:
--   A successful first local search is used literally.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/Base.lean#L154-L160
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/Base.lean#L154-L160

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

theorem QEC.Coding.BDL26TransposedStoppedDecoder.dualBaseDecode_first_local (S : OddScale)
    (sigma : Word BDL26Field (dualPresentation S 2).Z)
    (e : Word BDL26Field (dualPresentation S 2).Q)
    (h : search (fun e => dualBaseLocal S e &&
      decide (tannerCoboundary1 (dualPresentation S 2) e = sigma)) (dualBaseTable S) = some e) :
    dualBaseDecode S sigma = e := by sorry
