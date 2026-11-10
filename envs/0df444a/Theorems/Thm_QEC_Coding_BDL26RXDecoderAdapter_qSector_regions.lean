-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_qSector_regions
-- name    : QEC.Coding.BDL26RXDecoderAdapter.qSector_regions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:55:40.770563+00:00
-- url     : https://prove2.me/theorems/4945f2d3-6a03-4190-b397-764369012701
-- title:
--   BDL26 RXDecoder Adapter: q Sector regions
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the q Sector regions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Sectors.lean#L30-L33
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Sectors.lean#L30-L33

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Regions
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Sectors
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.qSector_regions (P : TannerSquarePresentation) (S : OddScale) :
    qSector P S = rxRegionUnion (localQ P S) := by sorry
