-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_xSector_regions
-- name    : QEC.Coding.BDL26RXDecoderAdapter.xSector_regions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:55:41.71223+00:00
-- url     : https://prove2.me/theorems/c02ef582-85c1-4b9d-bda5-1da368bdf83f
-- title:
--   BDL26 RXDecoder Adapter: x Sector regions
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the x Sector regions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Sectors.lean#L25-L28
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Sectors.lean#L25-L28

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Regions
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Sectors
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.xSector_regions (P : TannerSquarePresentation) (S : OddScale) :
    xSector P S = rxRegionUnion (localX P S) := by sorry
