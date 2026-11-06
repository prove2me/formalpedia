-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_hamiltonianEnergyProjector_fixed_iff
-- name    : QEC.Semantics.Davies.hamiltonianEnergyProjector_fixed_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:11:54.241198+00:00
-- url     : https://prove2.me/theorems/bd2e98e6-87d1-44be-b17b-31d673a4cf24
-- title:
--   Davies: hamiltonian Energy Projector fixed iff
-- statement:
--   The Davies construction uses the hamiltonian Energy Projector fixed iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Hamiltonian.lean#L101-L105
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Hamiltonian.lean#L101-L105

import Definitions.Def_QEC_Semantics_Dynamics_Davies_NormBound
import Definitions.Def_QEC_Semantics_Dynamics_ProtectedObservableDecay
import Definitions.Def_QEC_Semantics_Dynamics_Davies_Hamiltonian
set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.Davies
open Classical ThermalEncoding
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V] [Nontrivial V]
variable {κ : Type*} [Fintype κ]

theorem QEC.Semantics.Davies.hamiltonianEnergyProjector_fixed_iff (H : Operator V) (hH : H.IsSymmetric)
    (E : ℝ) (x : V) :
    hamiltonianEnergyProjector H hH E x = x ↔ H x = (E : ℂ) • x := by sorry
