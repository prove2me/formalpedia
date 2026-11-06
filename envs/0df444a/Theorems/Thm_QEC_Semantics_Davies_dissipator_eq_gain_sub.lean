-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_dissipator_eq_gain_sub
-- name    : QEC.Semantics.Davies.dissipator_eq_gain_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:27:48.895834+00:00
-- url     : https://prove2.me/theorems/2299e99c-389b-4bd4-977d-05f153012340
-- title:
--   Davies: dissipator eq gain sub
-- statement:
--   The Davies construction uses the dissipator eq gain sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/TraceBound.lean#L65-L70
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/TraceBound.lean#L65-L70

import Definitions.Def_QEC_Semantics_Dynamics_FourBlockGenerator
import Definitions.Def_QEC_Semantics_Dynamics_Davies_TraceBound
set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.Davies
open Classical
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V] [Nontrivial V]
variable {κ : Type*} [Fintype κ]

theorem QEC.Semantics.Davies.dissipator_eq_gain_sub (J : κ → Operator V) (F : Operator V) :
    lindbladDissipator J F = lindbladJumpGain J F -
      (2 : ℂ)⁻¹ • (squareSum J * F + F * squareSum J) := by sorry
