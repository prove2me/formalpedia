-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDifferentialMasks_incidenceHull_eq_iff
-- name    : QEC.Coding.BDL26RXDifferentialMasks.incidenceHull_eq_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T09:02:00.643969+00:00
-- url     : https://prove2.me/theorems/cad7a875-8ec3-4f71-811e-eb2a62975882
-- title:
--   BDL26 RXDifferential Masks: incidence Hull eq iff
-- statement:
--   The BDL26 RXDifferential Masks construction uses the incidence Hull eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXDifferentialMasks.lean#L220-L229
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXDifferentialMasks.lean#L220-L229

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXQConcreteCoherence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXDifferentialMasks
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXDifferentialMasks
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXQConcreteCoherence
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)

theorem QEC.Coding.BDL26RXDifferentialMasks.incidenceHull_eq_iff (A : Finset (state S i.val).presentation.Q) :
    incidenceHull S depth i A = A ↔ IncidenceSaturated S depth i A := by sorry
