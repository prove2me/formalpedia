-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_mem_rzPropagation
-- name    : QEC.Coding.BDL26HistorySyndromeSensitivity.mem_rzPropagation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:49:47.822394+00:00
-- url     : https://prove2.me/theorems/97bdf749-12e4-4970-942f-d3f6c1b36978
-- title:
--   BDL26 History Syndrome Sensitivity: mem rz Propagation
-- statement:
--   The BDL26 History Syndrome Sensitivity construction uses the mem rz Propagation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Steps.lean#L103-L112
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Steps.lean#L103-L112

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

theorem QEC.Coding.BDL26HistorySyndromeSensitivity.mem_rzPropagation (h : ¬ i.val % 2 = 0)
    (A : Finset (FamilyZ S depth i.succ)) (z : FamilyZ S depth i.castSucc) :
    z ∈ rzPropagation S depth i h A ↔
      ∃ p ∈ A, p ∈ (rzData S depth i h).coarseRegion z := by sorry
