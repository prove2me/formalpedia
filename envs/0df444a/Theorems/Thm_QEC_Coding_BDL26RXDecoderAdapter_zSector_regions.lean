-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_zSector_regions
-- name    : QEC.Coding.BDL26RXDecoderAdapter.zSector_regions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:56:06.287377+00:00
-- url     : https://prove2.me/theorems/38cd6aae-8679-4797-b913-7b992b56f29f
-- title:
--   BDL26 RXDecoder Adapter: z Sector regions
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the z Sector regions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Sectors.lean#L35-L38
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Sectors.lean#L35-L38

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Regions
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Sectors
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.zSector_regions (P : TannerSquarePresentation) (S : OddScale) :
    zSector P S = rxRegionUnion (localZ P S) := by sorry
