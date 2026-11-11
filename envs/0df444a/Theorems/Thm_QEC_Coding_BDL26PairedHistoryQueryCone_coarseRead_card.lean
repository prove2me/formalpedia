-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_coarseRead_card
-- name    : QEC.Coding.BDL26PairedHistoryQueryCone.coarseRead_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:07:17.00529+00:00
-- url     : https://prove2.me/theorems/bc7a3369-fd43-4757-8b57-cd7360d00577
-- title:
--   BDL26 Paired History Query Cone: coarse Read card
-- statement:
--   The BDL26 Paired History Query Cone construction uses the coarse Read card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone/ReadBounds.lean#L138-L144
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone/ReadBounds.lean#L138-L144

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

theorem QEC.Coding.BDL26PairedHistoryQueryCone.coarseRead_card (z : FamilyZ S depth i.castSucc) :
    (coarseRead S depth i z).card ≤ queryBlockBound S := by sorry
