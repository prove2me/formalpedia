-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_map2_diagonal
-- name    : QEC.Coding.BDL26RXDecoderAdapter.map2_diagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:57:37.306567+00:00
-- url     : https://prove2.me/theorems/4c70e43e-811a-40e4-b2ef-a3ad5a4569b4
-- title:
--   BDL26 RXDecoder Adapter: map2 diagonal
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the map2 diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Sectors.lean#L137-L139
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Sectors.lean#L137-L139

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Regions
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Sectors
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.map2_diagonal (P : TannerSquarePresentation) (S : OddScale)
    (w : Word BDL26Field P.Z) (z : P.Z) (c : Fin 2) :
    rxMap2Coord P S w (zPairEquiv P S (z,c)).val = w z := by sorry
