-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_correction_sectors_disjoint
-- name    : QEC.Coding.BDL26RXDecoderAdapter.correction_sectors_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:02:09.07739+00:00
-- url     : https://prove2.me/theorems/01918826-921d-4068-a98a-20ab220ac991
-- title:
--   BDL26 RXDecoder Adapter: correction sectors disjoint
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the correction sectors disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Sectors.lean#L108-L117
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Sectors.lean#L108-L117

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Regions
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Sectors
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.correction_sectors_disjoint (P : TannerSquarePresentation) (S : OddScale) :
    Disjoint (RXCoarseGraining.correctionRegionUnion (localX P S))
      (qCorrectionSector P S) := by sorry
