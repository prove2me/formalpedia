-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZDecoderAdapter_presentationOutput_correction
-- name    : QEC.Coding.BDL26RZDecoderAdapter.presentationOutput_correction
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T05:55:53.987963+00:00
-- url     : https://prove2.me/theorems/9758f0f6-8f37-4927-921e-3997ad2a71fe
-- title:
--   BDL26 RZDecoder Adapter: presentation Output correction
-- statement:
--   The BDL26 RZDecoder Adapter construction uses the presentation Output correction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZDecoderAdapter.lean#L738-L743
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZDecoderAdapter.lean#L738-L743

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_IndexedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZSupportedBoundary
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZDecoderAdapter
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RZDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26ReplacementSupport BDL26RZConcreteParity BDL26LevelTwoDistance
open MultiscaleDecoder RZCoarseGraining RZCoarseGrainingData
open BDL26AlternatingCochain BDL26ReplacementCochainMaps
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RZDecoderAdapter.presentationOutput_correction (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale)
    (sigma : (presentationFamily P A S).Syndrome (1 : LevelIndex 1)) :
    (presentationOutput P A S sigma).correction =
      correctionFromSyndrome (presentationData P A S)
        (presentationData_localTopCohomology P A S) sigma.val := by sorry

attribute [defeq] QEC.Coding.BDL26RZDecoderAdapter.presentationOutput_correction
