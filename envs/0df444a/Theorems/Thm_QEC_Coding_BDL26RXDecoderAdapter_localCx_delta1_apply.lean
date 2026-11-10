-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_localCx_delta1_apply
-- name    : QEC.Coding.BDL26RXDecoderAdapter.localCx_delta1_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:09:36.505925+00:00
-- url     : https://prove2.me/theorems/65da3318-aba4-405e-a38d-f90322d9f993
-- title:
--   BDL26 RXDecoder Adapter: local Cx delta1 apply
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the local Cx delta1 apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Coordinates.lean#L49-L57
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Coordinates.lean#L49-L57

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_LocalComplexes
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Coordinates
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.localCx_delta1_apply (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (w : Word BDL26Field (LocalRegionIndex ((localX P S).correctionRegion x)))
    (f : DoubleCylinderFace P x S) :
    wordLinearMapTranspose (localCx P S x).boundary2 w (xSyndromeEquiv P S x f) =
      wordLinearMapTranspose (doubleCylinderBoundary2 P x S)
        ((wordEquiv (xCorrectionEquiv P S x)).symm w) f := by sorry
