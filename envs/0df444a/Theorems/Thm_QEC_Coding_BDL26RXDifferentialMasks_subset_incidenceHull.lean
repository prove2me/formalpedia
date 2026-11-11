-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDifferentialMasks_subset_incidenceHull
-- name    : QEC.Coding.BDL26RXDifferentialMasks.subset_incidenceHull
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:38:24.63252+00:00
-- url     : https://prove2.me/theorems/a6684730-f4e0-48a9-af65-b821e20d1cd0
-- title:
--   BDL26 RXDifferential Masks: subset incidence Hull
-- statement:
--   The BDL26 RXDifferential Masks construction uses the subset incidence Hull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXDifferentialMasks.lean#L202-L205
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXDifferentialMasks.lean#L202-L205

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXQConcreteCoherence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXDifferentialMasks
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXDifferentialMasks
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXQConcreteCoherence
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)

theorem QEC.Coding.BDL26RXDifferentialMasks.subset_incidenceHull (A : Finset (state S i.val).presentation.Q) :
    A ⊆ incidenceHull S depth i A := by sorry
