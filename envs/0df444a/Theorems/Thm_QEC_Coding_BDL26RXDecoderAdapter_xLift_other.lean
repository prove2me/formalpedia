-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xLift_other
-- name    : QEC.Coding.BDL26RXDecoderAdapter.xLift_other
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:13:25.076428+00:00
-- url     : https://prove2.me/theorems/c67af9e1-5fcb-41b7-b520-6c01fa097bb0
-- title:
--   BDL26 RXDecoder Adapter: x Lift other
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the x Lift other property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Lifts.lean#L25-L28
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Lifts.lean#L25-L28

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Coordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Lifts
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.xLift_other (P : TannerSquarePresentation) (S : OddScale) (x y : P.X)
    (h : y ≠ x) (w : Word BDL26Field (DoubleCylinderVertex P x S))
    (v : DoubleCylinderVertex P y S) : xLift P S x w ⟨y,v⟩ = 0 := by sorry
