-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xLift_sum_at
-- name    : QEC.Coding.BDL26RXDecoderAdapter.xLift_sum_at
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:53:39.209344+00:00
-- url     : https://prove2.me/theorems/d4bdd78f-a3c7-416e-8ae8-417aabcc5540
-- title:
--   BDL26 RXDecoder Adapter: x Lift sum at
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the x Lift sum at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Lifts.lean#L45-L52
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Lifts.lean#L45-L52

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Coordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Lifts
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.xLift_sum_at (P : TannerSquarePresentation) (S : OddScale)
    (w : ∀ x : P.X, Word BDL26Field (DoubleCylinderVertex P x S))
    (x : P.X) (v : DoubleCylinderVertex P x S) :
    (∑ y : P.X, xLift P S y (w y)) ⟨x,v⟩ = w x v := by sorry
