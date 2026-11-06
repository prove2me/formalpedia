-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_hamiltonianEnergyProjector_commute
-- name    : QEC.Semantics.Davies.hamiltonianEnergyProjector_commute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:12:48.694044+00:00
-- url     : https://prove2.me/theorems/92496327-2c48-4947-a8ab-17966401517b
-- title:
--   Davies: hamiltonian Energy Projector commute
-- statement:
--   The Davies construction uses the hamiltonian Energy Projector commute property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Hamiltonian.lean#L107-L111
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Hamiltonian.lean#L107-L111

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

theorem QEC.Semantics.Davies.hamiltonianEnergyProjector_commute (H : Operator V) (hH : H.IsSymmetric)
    (O : Operator V) (hO : Commute H O) (E : ℝ) :
    Commute (hamiltonianEnergyProjector H hH E) O := by sorry
