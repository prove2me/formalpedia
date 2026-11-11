-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZDecoderAdapter_presentationOutput_components
-- name    : QEC.Coding.BDL26RZDecoderAdapter.presentationOutput_components
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:56:44.144221+00:00
-- url     : https://prove2.me/theorems/674b9dd2-a1ff-4c38-a238-c253338bdc97
-- title:
--   BDL26 RZDecoder Adapter: presentation Output components
-- statement:
--   The BDL26 RZDecoder Adapter construction uses the presentation Output components property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZDecoderAdapter.lean#L752-L758
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZDecoderAdapter.lean#L752-L758

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

theorem QEC.Coding.BDL26RZDecoderAdapter.presentationOutput_components (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale)
    (sigma : (presentationFamily P A S).Syndrome (1 : LevelIndex 1)) :
    (presentationOutput P A S sigma).localComponents =
      (Finset.univ : Finset P.Z).toList.map
        (fun z => localCorrectionComponent (presentationData P A S)
          (presentationData_localTopCohomology P A S) z sigma.val) := by sorry

attribute [defeq] QEC.Coding.BDL26RZDecoderAdapter.presentationOutput_components
