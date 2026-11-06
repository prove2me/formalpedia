-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_hamiltonianGibbs_commutes
-- name    : QEC.Semantics.Davies.hamiltonianGibbs_commutes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:11:37.628074+00:00
-- url     : https://prove2.me/theorems/508e65fd-9b5e-4499-bc88-d7c3874e640d
-- title:
--   Davies: hamiltonian Gibbs commutes
-- statement:
--   The Davies construction uses the hamiltonian Gibbs commutes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Hamiltonian.lean#L35-L39
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Hamiltonian.lean#L35-L39

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

theorem QEC.Semantics.Davies.hamiltonianGibbs_commutes (H : Operator V) (hH : H.IsSymmetric) (β : ℝ) :
    Commute H (hamiltonianGibbs H hH β).toOperator := by sorry
