-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_presentationOutput_coarse
-- name    : QEC.Coding.BDL26RXDecoderAdapter.presentationOutput_coarse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:01:32.796476+00:00
-- url     : https://prove2.me/theorems/f6bb65f4-2b91-4eeb-8beb-34b326f60d8f
-- title:
--   BDL26 RXDecoder Adapter: presentation Output coarse
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the presentation Output coarse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter.lean#L1470-L1475
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter.lean#L1470-L1475

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Decomposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Coordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Lifts
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Representative
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Graph
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Sectors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Induced
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Budgets
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_LocalComplexes
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_IndexedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph BDL26AlternatingCochain MultiscaleDecoder RXCoarseGraining
open BDL26RZMap1CoordinateBridge (tannerCoboundary0 tannerCoboundary1)
open scoped Classical BigOperators
open RXCoarseGrainingData

theorem QEC.Coding.BDL26RXDecoderAdapter.presentationOutput_coarse
    (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (S : OddScale)
    (sigma : (presentationFamily P A R S).Syndrome (1 : LevelIndex 1)) :
    (presentationOutput P A R S sigma).coarse.val =
      rxCoarseWord (presentationData P A R S) sigma.val := by sorry

attribute [defeq] QEC.Coding.BDL26RXDecoderAdapter.presentationOutput_coarse
