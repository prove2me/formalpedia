-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_x_restrict_correction
-- name    : QEC.Coding.BDL26RXDecoderAdapter.x_restrict_correction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:47:48.729094+00:00
-- url     : https://prove2.me/theorems/ae6787d9-8da0-447c-8781-58ba1845387c
-- title:
--   BDL26 RXDecoder Adapter: x restrict correction
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the x restrict correction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Coordinates.lean#L13-L19
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Coordinates.lean#L13-L19

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_LocalComplexes
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Coordinates
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.x_restrict_correction (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (w : Word BDL26Field (RX1 P S)) :
    (wordEquiv (xCorrectionEquiv P S x)).symm
      (restrictWordLinear ((localX P S).correctionRegion x) w) =
        fun e => w (Sum.inl ⟨x,e⟩) := by sorry
