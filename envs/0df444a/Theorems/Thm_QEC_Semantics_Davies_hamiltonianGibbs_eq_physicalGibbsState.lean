-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_hamiltonianGibbs_eq_physicalGibbsState
-- name    : QEC.Semantics.Davies.hamiltonianGibbs_eq_physicalGibbsState
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:11:38.704035+00:00
-- url     : https://prove2.me/theorems/fd8d4df1-a15f-40d8-a797-8bb540f45618
-- title:
--   Davies: hamiltonian Gibbs eq physical Gibbs State
-- statement:
--   The existing M11 physical Gibbs density is the one fixed by this Davies bath.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Hamiltonian.lean#L87-L95
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Hamiltonian.lean#L87-L95

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

theorem QEC.Semantics.Davies.hamiltonianGibbs_eq_physicalGibbsState (logical : PauliLikePair V)
    (H : Operator V) (hH : H.IsSymmetric) (hX : Commute H logical.x)
    (hZ : Commute H logical.z) (β : ℝ) :
    (hamiltonianGibbs H hH β).toOperator =
      (logical.physicalGibbsState H hZ hH β).toOperator := by sorry
