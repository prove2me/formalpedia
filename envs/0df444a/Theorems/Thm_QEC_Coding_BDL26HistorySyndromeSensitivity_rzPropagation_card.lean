-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_rzPropagation_card
-- name    : QEC.Coding.BDL26HistorySyndromeSensitivity.rzPropagation_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:47:40.753869+00:00
-- url     : https://prove2.me/theorems/ac9ff33a-1e27-413d-87d5-4a07bf9ab21f
-- title:
--   BDL26 History Syndrome Sensitivity: rz Propagation card
-- statement:
--   The BDL26 History Syndrome Sensitivity construction uses the rz Propagation card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Steps.lean#L114-L116
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Steps.lean#L114-L116

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

theorem QEC.Coding.BDL26HistorySyndromeSensitivity.rzPropagation_card (h : ¬ i.val % 2 = 0)
    (A : Finset (FamilyZ S depth i.succ)) :
    (rzPropagation S depth i h A).card ≤ A.card := by sorry
