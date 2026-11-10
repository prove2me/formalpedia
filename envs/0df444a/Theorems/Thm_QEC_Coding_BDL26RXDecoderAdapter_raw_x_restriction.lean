-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_raw_x_restriction
-- name    : QEC.Coding.BDL26RXDecoderAdapter.raw_x_restriction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:47:59.23682+00:00
-- url     : https://prove2.me/theorems/6f823422-45c6-4794-aa8d-b537d5875f4f
-- title:
--   BDL26 RXDecoder Adapter: raw x restriction
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the raw x restriction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Coordinates.lean#L30-L47
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Coordinates.lean#L30-L47

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_LocalComplexes
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Coordinates
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.raw_x_restriction (P : TannerSquarePresentation) (S : OddScale)
    (w : Word BDL26Field (RX1 P S)) (x : P.X) (f : DoubleCylinderFace P x S) :
    rxCoboundary1 P S w (Sum.inl (Sum.inl ⟨x,f⟩)) =
      wordLinearMapTranspose (doubleCylinderBoundary2 P x S)
        (fun e => w (Sum.inl ⟨x,e⟩)) f := by sorry
