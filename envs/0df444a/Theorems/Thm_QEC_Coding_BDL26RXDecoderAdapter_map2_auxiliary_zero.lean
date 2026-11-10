-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_map2_auxiliary_zero
-- name    : QEC.Coding.BDL26RXDecoderAdapter.map2_auxiliary_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:57:34.996375+00:00
-- url     : https://prove2.me/theorems/53ed02ab-3e2e-4331-afd3-f478b04c62e3
-- title:
--   BDL26 RXDecoder Adapter: map2 auxiliary zero
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the map2 auxiliary zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Sectors.lean#L141-L147
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Sectors.lean#L141-L147

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Regions
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Sectors
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.map2_auxiliary_zero (P : TannerSquarePresentation) (S : OddScale)
    (w : Word BDL26Field P.Z) (p : RX2 P S) (hp : p ∉ zSector P S) :
    rxMap2Coord P S w p = 0 := by sorry
