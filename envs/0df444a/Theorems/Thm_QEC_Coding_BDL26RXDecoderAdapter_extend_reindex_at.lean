-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_extend_reindex_at
-- name    : QEC.Coding.BDL26RXDecoderAdapter.extend_reindex_at
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:11:53.939051+00:00
-- url     : https://prove2.me/theorems/fd632fcc-5a14-4732-921c-995e4ed55747
-- title:
--   BDL26 RXDecoder Adapter: extend reindex at
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the extend reindex at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Flow.lean#L28-L34
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Flow.lean#L28-L34

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Coordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.extend_reindex_at {A B : Type} [Fintype B] [DecidableEq B]
    (Y : Finset B) (e : A ≃ LocalRegionIndex Y) (w : Word BDL26Field A) (a : A) :
    extendWordLinear Y (wordEquiv e w) (e a).1 = w a := by sorry
