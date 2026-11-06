-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_hamiltonianJump_protected
-- name    : QEC.Semantics.Davies.hamiltonianJump_protected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:11:35.97794+00:00
-- url     : https://prove2.me/theorems/4139b0cf-ec0f-4a40-b3d7-1135b688f078
-- title:
--   Davies: hamiltonian Jump protected
-- statement:
--   The Davies construction uses the hamiltonian Jump protected property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Hamiltonian.lean#L52-L61
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Hamiltonian.lean#L52-L61

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

theorem QEC.Semantics.Davies.hamiltonianJump_protected (H : Operator V) (hH : H.IsSymmetric)
    (A : κ → Operator V) (rate : κ → HamiltonianFrequency H hH → ℝ)
    (O P : Operator V) (hO : Commute H O) (hP : Commute H P)
    (hAP : ∀ a, (A a * O - O * A a) * P = 0) :
    JumpProtected (hamiltonianJump H hH A rate) O P := by sorry
