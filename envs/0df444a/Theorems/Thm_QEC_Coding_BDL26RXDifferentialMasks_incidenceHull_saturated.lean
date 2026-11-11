-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDifferentialMasks_incidenceHull_saturated
-- name    : QEC.Coding.BDL26RXDifferentialMasks.incidenceHull_saturated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:37:56.279415+00:00
-- url     : https://prove2.me/theorems/6cda463f-ccda-4434-933b-50b4c55f6eb5
-- title:
--   BDL26 RXDifferential Masks: incidence Hull saturated
-- statement:
--   The BDL26 RXDifferential Masks construction uses the incidence Hull saturated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXDifferentialMasks.lean#L207-L212
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXDifferentialMasks.lean#L207-L212

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXQConcreteCoherence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXDifferentialMasks
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXDifferentialMasks
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXQConcreteCoherence
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)

theorem QEC.Coding.BDL26RXDifferentialMasks.incidenceHull_saturated (A : Finset (state S i.val).presentation.Q) :
    IncidenceSaturated S depth i (incidenceHull S depth i A) := by sorry
