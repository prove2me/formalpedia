-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_rz_region_card
-- name    : QEC.Coding.BDL26PairedHistoryQueryCone.rz_region_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:41:00.545216+00:00
-- url     : https://prove2.me/theorems/cf00b7ff-4296-4d2a-94cf-b7f3cf94f505
-- title:
--   BDL26 Paired History Query Cone: rz region card
-- statement:
--   The BDL26 Paired History Query Cone construction uses the rz region card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone/ReadBounds.lean#L89-L111
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone/ReadBounds.lean#L89-L111

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

theorem QEC.Coding.BDL26PairedHistoryQueryCone.rz_region_card (h : ¬ i.val % 2 = 0)
    (z : FamilyZ S depth i.castSucc) :
    ((rzData S depth i h).coarseRegion z).card ≤ localCoordinateBound S := by sorry
