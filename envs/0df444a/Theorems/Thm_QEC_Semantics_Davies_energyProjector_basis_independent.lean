-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_energyProjector_basis_independent
-- name    : QEC.Semantics.Davies.energyProjector_basis_independent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:06:36.29352+00:00
-- url     : https://prove2.me/theorems/57be542b-9041-471f-bfa6-ae0db61d8346
-- title:
--   Davies: energy Projector basis independent
-- statement:
--   Energy projectors depend on the Hamiltonian, not on an eigenbasis choice.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L433-L444
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L433-L444

import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Definitions.Def_QEC_Semantics_Dynamics_FourBlockGenerator
import Definitions.Def_QEC_Semantics_Dynamics_Davies_Spectral
set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.Davies
open Classical
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem QEC.Semantics.Davies.energyProjector_basis_independent {ι' : Type} [Fintype ι'] [DecidableEq ι']
    (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (c : OrthonormalBasis ι' ℂ V) (f : ι' → ℝ)
    (hH : diagonal b e = diagonal c f) (E : ℝ) :
    energyProjector b e E = energyProjector c f E := by sorry
