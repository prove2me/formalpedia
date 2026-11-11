-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_ownerReaders_card
-- name    : QEC.Coding.BDL26PairedHistoryQueryCone.ownerReaders_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:07:09.816556+00:00
-- url     : https://prove2.me/theorems/5e087f02-dba4-46ee-8024-b9f565a27f6f
-- title:
--   BDL26 Paired History Query Cone: owner Readers card
-- statement:
--   The BDL26 Paired History Query Cone construction uses the owner Readers card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone/ReadBounds.lean#L146-L173
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone/ReadBounds.lean#L146-L173

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

theorem QEC.Coding.BDL26PairedHistoryQueryCone.ownerReaders_card (p : FamilyZ S depth i.succ) :
    ((Finset.univ : Finset (Owners S depth i)).filter
      (fun v => p ∈ ownerRead S depth i v)).card ≤ 57 := by sorry
