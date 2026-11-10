-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xFlow_at_x
-- name    : QEC.Coding.BDL26RXDecoderAdapter.xFlow_at_x
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:11:57.529794+00:00
-- url     : https://prove2.me/theorems/076e0d12-960e-4183-b86d-3d1fda1f8de7
-- title:
--   BDL26 RXDecoder Adapter: x Flow at x
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the x Flow at x property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Flow.lean#L132-L138
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Flow.lean#L132-L138

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Coordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.xFlow_at_x (P : TannerSquarePresentation) (S : OddScale) (x y : P.X)
    (w : Word BDL26Field (DoubleCylinderEdge P x S)) (f : DoubleCylinderFace P y S) :
    xFlow P S x w (Sum.inl (Sum.inl ⟨y,f⟩)) = 0 := by sorry
