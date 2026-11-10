-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_qExtend_other
-- name    : QEC.Coding.BDL26RXDecoderAdapter.qExtend_other
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:22:18.985207+00:00
-- url     : https://prove2.me/theorems/5ff85ab0-24c5-4841-bf3a-a8e60bd321a4
-- title:
--   BDL26 RXDecoder Adapter: q Extend other
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the q Extend other property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Flow.lean#L72-L78
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Flow.lean#L72-L78

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Coordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.qExtend_other (P : TannerSquarePresentation) (S : OddScale) (q r : P.Q)
    (h : r ≠ q) (w : Word BDL26Field (QDoubleCylinderVertex P q S))
    (v : QDoubleCylinderVertex P r S) : qExtend P S q w (Sum.inr ⟨r,v⟩) = 0 := by sorry
