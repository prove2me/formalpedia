-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_localCq_delta1_apply
-- name    : QEC.Coding.BDL26RXDecoderAdapter.localCq_delta1_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:08:42.884256+00:00
-- url     : https://prove2.me/theorems/b970631e-e304-4695-b1ba-c86cdfa66cfa
-- title:
--   BDL26 RXDecoder Adapter: local Cq delta1 apply
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the local Cq delta1 apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Coordinates.lean#L59-L67
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Coordinates.lean#L59-L67

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_LocalComplexes
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Coordinates
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.localCq_delta1_apply (P : TannerSquarePresentation) (S : OddScale) (q : P.Q)
    (w : Word BDL26Field (LocalRegionIndex ((localQ P S).correctionRegion q)))
    (e : QDoubleCylinderEdge P q S) :
    wordLinearMapTranspose (localCq P S q).boundary2 w (qSyndromeEquiv P S q e) =
      wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S)
        ((wordEquiv (qCorrectionEquiv P S q)).symm w) e := by sorry
