-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_hamiltonian_diagonal
-- name    : QEC.Semantics.Davies.hamiltonian_diagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:57:15.261954+00:00
-- url     : https://prove2.me/theorems/a585f3cf-5f91-4156-a4a4-3f217b159c23
-- title:
--   Davies: hamiltonian diagonal
-- statement:
--   The Davies construction uses the hamiltonian diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L239-L248
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L239-L248

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

theorem QEC.Semantics.Davies.hamiltonian_diagonal (H : Operator V) (hH : H.IsSymmetric) :
    diagonal (hamiltonianBasis H hH) (hamiltonianEnergies H hH) = H := by sorry
