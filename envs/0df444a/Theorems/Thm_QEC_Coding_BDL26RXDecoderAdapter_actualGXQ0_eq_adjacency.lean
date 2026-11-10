-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_actualGXQ0_eq_adjacency
-- name    : QEC.Coding.BDL26RXDecoderAdapter.actualGXQ0_eq_adjacency
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:56:35.399936+00:00
-- url     : https://prove2.me/theorems/fc2753a5-68a5-420e-a2e3-0886bb366d50
-- title:
--   BDL26 RXDecoder Adapter: actual GXQ0 eq adjacency
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the actual GXQ0 eq adjacency property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Induced.lean#L33-L39
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Induced.lean#L33-L39

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Regions
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Induced
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.actualGXQ0_eq_adjacency (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) :
    actualGXQ0 P A S = rxXQAdjacency P := by sorry
