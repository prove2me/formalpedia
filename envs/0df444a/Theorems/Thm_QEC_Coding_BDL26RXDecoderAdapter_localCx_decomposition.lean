-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_localCx_decomposition
-- name    : QEC.Coding.BDL26RXDecoderAdapter.localCx_decomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:52:46.272624+00:00
-- url     : https://prove2.me/theorems/4450c315-d0ad-416e-a4a1-6346dc08f60f
-- title:
--   BDL26 RXDecoder Adapter: local Cx decomposition
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the local Cx decomposition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Decomposition.lean#L140-L156
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Decomposition.lean#L140-L156

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Decomposition
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.localCx_decomposition (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (f : Word BDL26Field (LocalRegionIndex ((localX P S).correctionRegion x))) :
    rxCoboundary1 P S (extendWordLinear ((localX P S).correctionRegion x) f) =
      extendWordLinear ((localX P S).syndromeRegion x)
        (wordLinearMapTranspose (localCx P S x).boundary2 f) +
          xFlow P S x ((wordEquiv (xCorrectionEquiv P S x)).symm f) := by sorry
