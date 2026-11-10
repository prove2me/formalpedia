-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_raw_delta0_x
-- name    : QEC.Coding.BDL26RXDecoderAdapter.raw_delta0_x
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:14:16.960219+00:00
-- url     : https://prove2.me/theorems/63954cd4-257a-425c-b1b5-5538598f9a99
-- title:
--   BDL26 RXDecoder Adapter: raw delta0 x
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the raw delta0 x property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Lifts.lean#L30-L43
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Lifts.lean#L30-L43

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Coordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Lifts
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.raw_delta0_x (P : TannerSquarePresentation) (S : OddScale)
    (w : Word BDL26Field (RX0 P S)) (x : P.X) (e : DoubleCylinderEdge P x S) :
    rxCoboundary0 P S w (Sum.inl ⟨x,e⟩) =
      wordLinearMapTranspose (doubleCylinderBoundary1 P x S)
        (fun v => w ⟨x,v⟩) e := by sorry
