-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_region_restrict_extend
-- name    : QEC.Coding.BDL26RXDecoderAdapter.region_restrict_extend
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:26:56.011548+00:00
-- url     : https://prove2.me/theorems/061c4559-5ec7-4c87-ade7-572da1025194
-- title:
--   BDL26 RXDecoder Adapter: region restrict extend
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the region restrict extend property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Decomposition.lean#L124-L129
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Decomposition.lean#L124-L129

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Decomposition
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.region_restrict_extend {A : Type} [Fintype A] [DecidableEq A]
    (Y : Finset A) (f : Word BDL26Field (LocalRegionIndex Y)) :
    restrictWordLinear Y (extendWordLinear Y f) = f := by sorry
