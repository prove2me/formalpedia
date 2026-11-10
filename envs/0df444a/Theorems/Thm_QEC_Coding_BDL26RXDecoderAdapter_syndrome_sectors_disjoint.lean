-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_syndrome_sectors_disjoint
-- name    : QEC.Coding.BDL26RXDecoderAdapter.syndrome_sectors_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:56:21.80956+00:00
-- url     : https://prove2.me/theorems/6712329a-685b-4ed2-a16d-420d2ac821e2
-- title:
--   BDL26 RXDecoder Adapter: syndrome sectors disjoint
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the syndrome sectors disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Sectors.lean#L74-L92
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Sectors.lean#L74-L92

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Regions
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Sectors
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.syndrome_sectors_disjoint (P : TannerSquarePresentation) (S : OddScale) :
    Disjoint (xSector P S) (qSector P S) ∧ Disjoint (xSector P S) (zSector P S) ∧
      Disjoint (qSector P S) (zSector P S) := by sorry
