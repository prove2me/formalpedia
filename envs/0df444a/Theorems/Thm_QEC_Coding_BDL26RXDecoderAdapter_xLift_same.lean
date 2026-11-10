-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xLift_same
-- name    : QEC.Coding.BDL26RXDecoderAdapter.xLift_same
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:13:16.756991+00:00
-- url     : https://prove2.me/theorems/ed5df720-dc44-48f2-bec3-1609be759993
-- title:
--   BDL26 RXDecoder Adapter: x Lift same
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the x Lift same property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Lifts.lean#L20-L23
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Lifts.lean#L20-L23

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Coordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Lifts
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.xLift_same (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (w : Word BDL26Field (DoubleCylinderVertex P x S))
    (v : DoubleCylinderVertex P x S) : xLift P S x w ⟨x,v⟩ = w v := by sorry
