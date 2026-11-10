-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xFlow_at_q
-- name    : QEC.Coding.BDL26RXDecoderAdapter.xFlow_at_q
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:12:19.881413+00:00
-- url     : https://prove2.me/theorems/791cdb63-91e4-4091-aad3-8f6f05392def
-- title:
--   BDL26 RXDecoder Adapter: x Flow at q
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the x Flow at q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Flow.lean#L92-L114
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Flow.lean#L92-L114

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Coordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.xFlow_at_q (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (x : P.X) (w : Word BDL26Field (DoubleCylinderEdge P x S))
    (q : P.Q) (e : QDoubleCylinderEdge P q S) :
    xFlow P S x w (Sum.inl (Sum.inr ⟨q,e⟩)) =
      if h : P.xq x q = true then rxXQDegreeOne P A q x h S w e else 0 := by sorry
