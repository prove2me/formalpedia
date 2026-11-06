-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_hamiltonianDissipator_selfAdjointTraceNorm_le
-- name    : QEC.Semantics.Davies.hamiltonianDissipator_selfAdjointTraceNorm_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:11:33.751392+00:00
-- url     : https://prove2.me/theorems/6939fe4e-cbd4-408d-9247-ca08e7b89535
-- title:
--   Davies: hamiltonian Dissipator self Adjoint Trace Norm le
-- statement:
--   The constant counts couplings, even with arbitrarily many or degenerate gaps.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Hamiltonian.lean#L64-L72
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Hamiltonian.lean#L64-L72

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

theorem QEC.Semantics.Davies.hamiltonianDissipator_selfAdjointTraceNorm_le
    (H : Operator V) (hH : H.IsSymmetric) (A : κ → Operator V)
    (hA : ∀ a, operatorNorm (A a) ≤ 1)
    (rate : κ → HamiltonianFrequency H hH → ℝ) (hmax : ℝ)
    (hm : 0 ≤ hmax) (hn : ∀ a w, 0 ≤ rate a w) (hu : ∀ a w, rate a w ≤ hmax) :
    selfAdjointTraceNormOneToOne (hamiltonianDissipator H hH A rate) ≤
      2 * Fintype.card κ * hmax := by sorry
