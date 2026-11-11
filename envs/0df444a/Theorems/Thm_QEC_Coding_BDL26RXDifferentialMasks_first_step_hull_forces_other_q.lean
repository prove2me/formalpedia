-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDifferentialMasks_first_step_hull_forces_other_q
-- name    : QEC.Coding.BDL26RXDifferentialMasks.first_step_hull_forces_other_q
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T22:35:55.392949+00:00
-- url     : https://prove2.me/theorems/fd394bd3-eae1-47c0-8382-3610ed2c2841
-- title:
--   BDL26 RXDifferential Masks: first step hull forces other q
-- statement:
--   The least closed singleton mask is STRICTLY larger in this actual example;
--   it contains the second real Q coordinate forced by the shared Z.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXDifferentialMasks.lean#L330-L345
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXDifferentialMasks.lean#L330-L345

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXQConcreteCoherence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXDifferentialMasks
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXDifferentialMasks
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXQConcreteCoherence
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
open BDL26FiniteAlternatingCore

theorem QEC.Coding.BDL26RXDifferentialMasks.first_step_hull_forces_other_q (S : OddScale) (depth : Nat) (hd : 0 < depth) :
    (4 : BaseQubit) ∈ incidenceHull S depth ⟨0,hd⟩ {(0 : BaseQubit)} ∧
      incidenceHull S depth ⟨0,hd⟩ {(0 : BaseQubit)} ≠ {(0 : BaseQubit)} := by sorry
