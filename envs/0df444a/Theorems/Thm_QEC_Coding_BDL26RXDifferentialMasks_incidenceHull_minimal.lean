-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDifferentialMasks_incidenceHull_minimal
-- name    : QEC.Coding.BDL26RXDifferentialMasks.incidenceHull_minimal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:38:57.873256+00:00
-- url     : https://prove2.me/theorems/051f41c5-0694-460d-b802-438d0f6c9518
-- title:
--   BDL26 RXDifferential Masks: incidence Hull minimal
-- statement:
--   The BDL26 RXDifferential Masks construction uses the incidence Hull minimal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXDifferentialMasks.lean#L214-L218
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXDifferentialMasks.lean#L214-L218

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXQConcreteCoherence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXDifferentialMasks
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXDifferentialMasks
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXQConcreteCoherence
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)

theorem QEC.Coding.BDL26RXDifferentialMasks.incidenceHull_minimal (A C : Finset (state S i.val).presentation.Q)
    (hA : A ⊆ C) (hs : IncidenceSaturated S depth i C) :
    incidenceHull S depth i A ⊆ C := by sorry
