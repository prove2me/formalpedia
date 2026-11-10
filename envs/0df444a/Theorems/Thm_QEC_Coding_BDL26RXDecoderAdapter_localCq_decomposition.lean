-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_localCq_decomposition
-- name    : QEC.Coding.BDL26RXDecoderAdapter.localCq_decomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:53:07.756438+00:00
-- url     : https://prove2.me/theorems/0426acfc-9946-4cda-a9f2-c1f6bd2d7d56
-- title:
--   BDL26 RXDecoder Adapter: local Cq decomposition
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the local Cq decomposition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Decomposition.lean#L158-L174
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Decomposition.lean#L158-L174

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Decomposition
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.localCq_decomposition (P : TannerSquarePresentation) (S : OddScale) (q : P.Q)
    (f : Word BDL26Field (LocalRegionIndex ((localQ P S).correctionRegion q))) :
    rxCoboundary1 P S (extendWordLinear ((localQ P S).correctionRegion q) f) =
      extendWordLinear ((localQ P S).syndromeRegion q)
        (wordLinearMapTranspose (localCq P S q).boundary2 f) +
          qFlow P S q ((wordEquiv (qCorrectionEquiv P S q)).symm f) := by sorry
