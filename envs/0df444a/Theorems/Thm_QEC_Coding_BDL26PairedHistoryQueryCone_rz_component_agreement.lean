-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_rz_component_agreement
-- name    : QEC.Coding.BDL26PairedHistoryQueryCone.rz_component_agreement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:03:11.122131+00:00
-- url     : https://prove2.me/theorems/094e6307-5c6e-4967-aa29-37ce83965f68
-- title:
--   BDL26 Paired History Query Cone: rz component agreement
-- statement:
--   The BDL26 Paired History Query Cone construction uses the rz component agreement property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone/LocalReads.lean#L98-L115
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone/LocalReads.lean#L98-L115

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

theorem QEC.Coding.BDL26PairedHistoryQueryCone.rz_component_agreement (h : ¬ i.val % 2 = 0)
    (z : FamilyZ S depth i.castSucc)
    (s t : Word BDL26Field (FamilyZ S depth i.succ))
    (ha : AgreeOn ((rzData S depth i h).coarseRegion z) s t) :
    RZCoarseGraining.localCorrectionComponent (rzData S depth i h)
      (rzData_localTopCohomology S depth i h) z s =
    RZCoarseGraining.localCorrectionComponent (rzData S depth i h)
      (rzData_localTopCohomology S depth i h) z t := by sorry
