-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_rz_pair_support
-- name    : QEC.Coding.BDL26HistorySyndromeSensitivity.rz_pair_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:47:38.968984+00:00
-- url     : https://prove2.me/theorems/92fbbf7d-3ed5-4276-93cb-d3b62fe3240a
-- title:
--   BDL26 History Syndrome Sensitivity: rz pair support
-- statement:
--   The BDL26 History Syndrome Sensitivity construction uses the rz pair support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Steps.lean#L118-L136
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Steps.lean#L118-L136

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXInfluenceBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Steps
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26RXDecoderAdapter BDL26RZDecoderAdapter
open BDL26RXCoarseInfluence BDL26RXInfluenceBounds MultiscaleDecoder
open RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)

theorem QEC.Coding.BDL26HistorySyndromeSensitivity.rz_pair_support (h : ¬ i.val % 2 = 0)
    (sigma tau : (indexedFamily S depth).Syndrome i.succ) :
    hammingSupport ((rzStepOutput S depth i h sigma).coarse.val +
      (rzStepOutput S depth i h tau).coarse.val) ⊆
      rzPropagation S depth i h (hammingSupport (sigma.val + tau.val)) := by sorry
