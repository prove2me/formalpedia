-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xFlow_at_z
-- name    : QEC.Coding.BDL26RXDecoderAdapter.xFlow_at_z
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:13:51.472639+00:00
-- url     : https://prove2.me/theorems/0b69860d-39d6-483b-bf4d-5a3a4a075003
-- title:
--   BDL26 RXDecoder Adapter: x Flow at z
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the x Flow at z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Flow.lean#L140-L146
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Flow.lean#L140-L146

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Coordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.xFlow_at_z (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (w : Word BDL26Field (DoubleCylinderEdge P x S)) (z : P.Z) (c : Fin 2) :
    xFlow P S x w (Sum.inr (z,c)) = 0 := by sorry
