-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDifferentialMasks_mem_incidenceHull
-- name    : QEC.Coding.BDL26RXDifferentialMasks.mem_incidenceHull
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:37:30.831598+00:00
-- url     : https://prove2.me/theorems/4880af2a-b6d0-451b-9b0c-83a0459afd4e
-- title:
--   BDL26 RXDifferential Masks: mem incidence Hull
-- statement:
--   The BDL26 RXDifferential Masks construction uses the mem incidence Hull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXDifferentialMasks.lean#L196-L200
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXDifferentialMasks.lean#L196-L200

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXQConcreteCoherence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXDifferentialMasks
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXDifferentialMasks
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXQConcreteCoherence
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)

theorem QEC.Coding.BDL26RXDifferentialMasks.mem_incidenceHull (A : Finset (state S i.val).presentation.Q)
    (q : (state S i.val).presentation.Q) : q ∈ incidenceHull S depth i A ↔
    ∀ C : Finset (state S i.val).presentation.Q,
      A ⊆ C → IncidenceSaturated S depth i C → q ∈ C := by sorry
