-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xExtend_other
-- name    : QEC.Coding.BDL26RXDecoderAdapter.xExtend_other
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:14:33.3122+00:00
-- url     : https://prove2.me/theorems/4df53288-f9b6-4f8f-82dd-082ce23e3df4
-- title:
--   BDL26 RXDecoder Adapter: x Extend other
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the x Extend other property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Flow.lean#L64-L70
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Flow.lean#L64-L70

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Coordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.xExtend_other (P : TannerSquarePresentation) (S : OddScale) (x y : P.X)
    (h : y ≠ x) (w : Word BDL26Field (DoubleCylinderEdge P x S))
    (e : DoubleCylinderEdge P y S) : xExtend P S x w (Sum.inl ⟨y,e⟩) = 0 := by sorry
