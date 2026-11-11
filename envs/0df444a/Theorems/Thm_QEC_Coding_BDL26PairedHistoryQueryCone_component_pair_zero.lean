-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_component_pair_zero
-- name    : QEC.Coding.BDL26PairedHistoryQueryCone.component_pair_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:04:39.199373+00:00
-- url     : https://prove2.me/theorems/24515419-7f66-47cf-9abb-781e25df77bb
-- title:
--   BDL26 Paired History Query Cone: component pair zero
-- statement:
--   The BDL26 Paired History Query Cone construction uses the component pair zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone/LocalReads.lean#L173-L186
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone/LocalReads.lean#L173-L186

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Intervals
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXQConcreteCoherence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone_LocalReads
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PairedHistoryQueryCone
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26RXDecoderAdapter BDL26RZDecoderAdapter BDL26RXCoarseInfluence
open BDL26RXInfluenceBounds BDL26GraphQuantitativeBounds
open MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)

theorem QEC.Coding.BDL26PairedHistoryQueryCone.component_pair_zero (U : Finset (FamilyZ S depth i.succ))
    (s t : Word BDL26Field (FamilyZ S depth i.succ))
    (hs : hammingSupport (s+t) ⊆ U) (v : Owners S depth i)
    (hv : v ∉ affected S depth i U) :
    component S depth i v s + component S depth i v t = 0 := by sorry
