-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_rxOwnerRead_card
-- name    : QEC.Coding.BDL26PairedHistoryQueryCone.rxOwnerRead_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:41:11.475688+00:00
-- url     : https://prove2.me/theorems/0ee26c19-eb69-407d-a6cd-faddf70ee60c
-- title:
--   BDL26 Paired History Query Cone: rx Owner Read card
-- statement:
--   The BDL26 Paired History Query Cone construction uses the rx Owner Read card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone/ReadBounds.lean#L116-L122
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone/ReadBounds.lean#L116-L122

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

theorem QEC.Coding.BDL26PairedHistoryQueryCone.rxOwnerRead_card (h : i.val % 2 = 0) (v : Owners S depth i) :
    (rxOwnerRead S depth i h v).card ≤ queryBlockBound S := by sorry
