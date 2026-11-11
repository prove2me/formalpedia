-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXInfluenceBounds_errorInfluence_card_le
-- name    : QEC.Coding.BDL26RXInfluenceBounds.errorInfluence_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:45:42.388083+00:00
-- url     : https://prove2.me/theorems/1d3e0a92-4c82-4fbd-b94a-ea8d31aaeb6d
-- title:
--   BDL26 RXInfluence Bounds: error Influence card le
-- statement:
--   The BDL26 RXInfluence Bounds construction uses the error Influence card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXInfluenceBounds.lean#L188-L192
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXInfluenceBounds.lean#L188-L192

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCoarseInfluence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformReadoutWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXInfluenceBounds
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXInfluenceBounds
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXDecoderAdapter BDL26RXCoarseInfluence BDL26BoundedValence
open BDL26GraphQuantitativeBounds BDL26RZMap1CoordinateBridge
open MultiscaleDecoder RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2 = 0)

theorem QEC.Coding.BDL26RXInfluenceBounds.errorInfluence_card_le (e : (indexedFamily S depth).Cochain1 i.succ) :
    (errorInfluence S depth i h e).card ≤ 228 * HammingWeight e := by sorry
