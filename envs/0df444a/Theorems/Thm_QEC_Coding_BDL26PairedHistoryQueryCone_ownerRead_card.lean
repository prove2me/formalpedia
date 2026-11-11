-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_ownerRead_card
-- name    : QEC.Coding.BDL26PairedHistoryQueryCone.ownerRead_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:07:08.187189+00:00
-- url     : https://prove2.me/theorems/51b7b15a-c5bc-49dc-994e-8d2b3798ef79
-- title:
--   BDL26 Paired History Query Cone: owner Read card
-- statement:
--   The BDL26 Paired History Query Cone construction uses the owner Read card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone/ReadBounds.lean#L124-L136
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone/ReadBounds.lean#L124-L136

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

theorem QEC.Coding.BDL26PairedHistoryQueryCone.ownerRead_card (v : Owners S depth i) :
    (ownerRead S depth i v).card ≤ queryBlockBound S := by sorry
