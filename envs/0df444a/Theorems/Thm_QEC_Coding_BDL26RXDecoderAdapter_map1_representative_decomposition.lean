-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_map1_representative_decomposition
-- name    : QEC.Coding.BDL26RXDecoderAdapter.map1_representative_decomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:27:09.442791+00:00
-- url     : https://prove2.me/theorems/8d4fb116-92ba-438e-acb8-3d723e17e6b6
-- title:
--   BDL26 RXDecoder Adapter: map1 representative decomposition
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the map1 representative decomposition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Representative.lean#L78-L104
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Representative.lean#L78-L104

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Coordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Representative
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.map1_representative_decomposition (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (w : Word BDL26Field P.Q) :
    rxMap1Coord P S w = ∑ q : P.Q, extendWordLinear ((localQ P S).correctionRegion q)
      (qRepresentative P A S q ((qCohomologyEquiv P A S).symm w q)).1 := by sorry
