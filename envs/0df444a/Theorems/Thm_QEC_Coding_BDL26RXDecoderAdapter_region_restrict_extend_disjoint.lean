-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_region_restrict_extend_disjoint
-- name    : QEC.Coding.BDL26RXDecoderAdapter.region_restrict_extend_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:26:48.815875+00:00
-- url     : https://prove2.me/theorems/d1b6a033-788e-412e-974b-c233aba42898
-- title:
--   BDL26 RXDecoder Adapter: region restrict extend disjoint
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the region restrict extend disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Decomposition.lean#L131-L138
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Decomposition.lean#L131-L138

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Decomposition
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.region_restrict_extend_disjoint {A : Type} [Fintype A] [DecidableEq A]
    (Y Z : Finset A) (h : Disjoint Y Z) (f : Word BDL26Field (LocalRegionIndex Y)) :
    restrictWordLinear Z (extendWordLinear Y f) = 0 := by sorry
