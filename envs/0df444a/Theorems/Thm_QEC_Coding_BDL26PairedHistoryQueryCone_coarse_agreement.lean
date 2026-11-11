-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_coarse_agreement
-- name    : QEC.Coding.BDL26PairedHistoryQueryCone.coarse_agreement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:03:20.342233+00:00
-- url     : https://prove2.me/theorems/7b67fd05-900d-4921-afd4-ed6a022484cd
-- title:
--   BDL26 Paired History Query Cone: coarse agreement
-- statement:
--   The BDL26 Paired History Query Cone construction uses the coarse agreement property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone/LocalReads.lean#L148-L160
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone/LocalReads.lean#L148-L160

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

theorem QEC.Coding.BDL26PairedHistoryQueryCone.coarse_agreement (s t : (indexedFamily S depth).Syndrome i.succ)
    (z : FamilyZ S depth i.castSucc)
    (ha : AgreeOn (coarseRead S depth i z) s.val t.val) :
    (actualStep S depth i s).coarse.val z = (actualStep S depth i t).coarse.val z := by sorry
