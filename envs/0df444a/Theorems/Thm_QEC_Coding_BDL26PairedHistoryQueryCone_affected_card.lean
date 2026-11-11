-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_affected_card
-- name    : QEC.Coding.BDL26PairedHistoryQueryCone.affected_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:07:36.749499+00:00
-- url     : https://prove2.me/theorems/132a7105-8555-4b2e-8068-4b8f6f0ffd53
-- title:
--   BDL26 Paired History Query Cone: affected card
-- statement:
--   The BDL26 Paired History Query Cone construction uses the affected card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone/ReadBounds.lean#L175-L184
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone/ReadBounds.lean#L175-L184

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone_LocalReads
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone_ReadBounds
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

theorem QEC.Coding.BDL26PairedHistoryQueryCone.affected_card (U : Finset (FamilyZ S depth i.succ)) :
    (affected S depth i U).card ≤ 57 * U.card := by sorry
