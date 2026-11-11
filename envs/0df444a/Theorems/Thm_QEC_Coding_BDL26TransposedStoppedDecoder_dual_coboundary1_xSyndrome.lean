-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_dual_coboundary1_xSyndrome
-- name    : QEC.Coding.BDL26TransposedStoppedDecoder.dual_coboundary1_xSyndrome
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T14:37:09.14787+00:00
-- url     : https://prove2.me/theorems/ff4c21ad-8924-4c51-8a1e-e8bfb94cfd90
-- title:
--   BDL26 Transposed Stopped Decoder: dual coboundary1 x Syndrome
-- statement:
--   The dual physical syndrome is exactly the existing actual X-check syndrome.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/Base.lean#L120-L122
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/Base.lean#L120-L122

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

theorem QEC.Coding.BDL26TransposedStoppedDecoder.dual_coboundary1_xSyndrome (S : OddScale) (n : Nat) :
    tannerCoboundary1 (dualPresentation S n) = BDL26CSSHamiltonian.xSyndrome S n := by sorry
