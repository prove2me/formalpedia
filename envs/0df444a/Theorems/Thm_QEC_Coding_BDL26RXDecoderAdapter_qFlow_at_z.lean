-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_qFlow_at_z
-- name    : QEC.Coding.BDL26RXDecoderAdapter.qFlow_at_z
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:14:56.218193+00:00
-- url     : https://prove2.me/theorems/a8ff8f6d-c961-47bd-984c-33591c8317d0
-- title:
--   BDL26 RXDecoder Adapter: q Flow at z
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the q Flow at z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Flow.lean#L116-L129
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Flow.lean#L116-L129

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Coordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.qFlow_at_z (P : TannerSquarePresentation) (S : OddScale) (q : P.Q)
    (w : Word BDL26Field (QDoubleCylinderVertex P q S)) (z : P.Z) (c : Fin 2) :
    qFlow P S q w (Sum.inr (z,c)) = rxQOutgoing P q S w z c := by sorry
