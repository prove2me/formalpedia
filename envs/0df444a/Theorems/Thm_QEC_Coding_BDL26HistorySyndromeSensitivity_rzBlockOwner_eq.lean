-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_rzBlockOwner_eq
-- name    : QEC.Coding.BDL26HistorySyndromeSensitivity.rzBlockOwner_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:59:42.651972+00:00
-- url     : https://prove2.me/theorems/e883f75c-4d04-4251-bfac-591f2e2e75f8
-- title:
--   BDL26 History Syndrome Sensitivity: rz Block Owner eq
-- statement:
--   The BDL26 History Syndrome Sensitivity construction uses the rz Block Owner eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Steps.lean#L93-L98
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Steps.lean#L93-L98

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

theorem QEC.Coding.BDL26HistorySyndromeSensitivity.rzBlockOwner_eq (h : ¬ i.val % 2 = 0) (p : FamilyZ S depth i.succ)
    (z : FamilyZ S depth i.castSucc) (hp : p ∈ (rzData S depth i h).coarseRegion z) :
    rzBlockOwner S depth i h p = z := by sorry
