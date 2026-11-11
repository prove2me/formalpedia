-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_liftQueries_card
-- name    : QEC.Coding.BDL26PairedHistoryQueryCone.liftQueries_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:41:29.466097+00:00
-- url     : https://prove2.me/theorems/7d9a1f23-bf72-4593-8cf7-76dae3e38dc1
-- title:
--   BDL26 Paired History Query Cone: lift Queries card
-- statement:
--   The BDL26 Paired History Query Cone construction uses the lift Queries card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone/ReadBounds.lean#L192-L195
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone/ReadBounds.lean#L192-L195

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

theorem QEC.Coding.BDL26PairedHistoryQueryCone.liftQueries_card (A : Finset (FamilyZ S depth i.castSucc)) :
    (liftQueries S depth i A).card ≤ queryBlockBound S * A.card := by sorry
