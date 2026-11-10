-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_qRepresentative_value
-- name    : QEC.Coding.BDL26RXDecoderAdapter.qRepresentative_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:19:39.14266+00:00
-- url     : https://prove2.me/theorems/5229f82a-32f4-43ed-849b-c88fd0f01d93
-- title:
--   BDL26 RXDecoder Adapter: q Representative value
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the q Representative value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Representative.lean#L69-L76
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Representative.lean#L69-L76

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Coordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Representative
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.qRepresentative_value (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (q : P.Q)
    (w : Word BDL26Field P.Q)
    (p : LocalRegionIndex ((localQ P S).correctionRegion q)) :
    (qRepresentative P A S q ((qCohomologyEquiv P A S).symm w q)).1 p = w q := by sorry
