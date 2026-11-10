-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZDecoderAdapter_presentationOutput_coarse
-- name    : QEC.Coding.BDL26RZDecoderAdapter.presentationOutput_coarse
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T05:56:21.358202+00:00
-- url     : https://prove2.me/theorems/ae552eed-87e6-4e5a-9e12-82d62cc7b17b
-- title:
--   BDL26 RZDecoder Adapter: presentation Output coarse
-- statement:
--   The BDL26 RZDecoder Adapter construction uses the presentation Output coarse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZDecoderAdapter.lean#L745-L750
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZDecoderAdapter.lean#L745-L750

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

theorem QEC.Coding.BDL26RZDecoderAdapter.presentationOutput_coarse (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale)
    (sigma : (presentationFamily P A S).Syndrome (1 : LevelIndex 1)) :
    (presentationOutput P A S sigma).coarse =
      coarseSyndrome (presentationData P A S)
        (presentationData_inducedCoboundaryCompatibility P A S) sigma := by sorry

attribute [defeq] QEC.Coding.BDL26RZDecoderAdapter.presentationOutput_coarse
