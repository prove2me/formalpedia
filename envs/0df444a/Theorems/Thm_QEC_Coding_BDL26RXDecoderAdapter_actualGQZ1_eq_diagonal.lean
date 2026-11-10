-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_actualGQZ1_eq_diagonal
-- name    : QEC.Coding.BDL26RXDecoderAdapter.actualGQZ1_eq_diagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:57:03.235274+00:00
-- url     : https://prove2.me/theorems/cb328ff4-990b-4398-b558-934e8ce49bf2
-- title:
--   BDL26 RXDecoder Adapter: actual GQZ1 eq diagonal
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the actual GQZ1 eq diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Induced.lean#L64-L75
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Induced.lean#L64-L75

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Regions
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Induced
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDecoderAdapter.actualGQZ1_eq_diagonal (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) :
    actualGQZ1 P S = RXCoarseGraining.diagonalMap.comp (rxQZAdjacency P) := by sorry
