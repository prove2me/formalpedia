-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_rzBlockOwner_mem
-- name    : QEC.Coding.BDL26HistorySyndromeSensitivity.rzBlockOwner_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:00:01.303725+00:00
-- url     : https://prove2.me/theorems/7c5aa050-5b17-4f53-9446-8baf142d5bdd
-- title:
--   BDL26 History Syndrome Sensitivity: rz Block Owner mem
-- statement:
--   The BDL26 History Syndrome Sensitivity construction uses the rz Block Owner mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Steps.lean#L89-L91
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Steps.lean#L89-L91

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

theorem QEC.Coding.BDL26HistorySyndromeSensitivity.rzBlockOwner_mem (h : ¬ i.val % 2 = 0) (p : FamilyZ S depth i.succ) :
    p ∈ (rzData S depth i h).coarseRegion (rzBlockOwner S depth i h p) := by sorry
