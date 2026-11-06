-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_hamiltonianGibbs_stationary
-- name    : QEC.Semantics.Davies.hamiltonianGibbs_stationary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:11:18.813263+00:00
-- url     : https://prove2.me/theorems/e2843f5d-e589-4907-b750-68aafc79640d
-- title:
--   Davies: hamiltonian Gibbs stationary
-- statement:
--   The Davies construction uses the hamiltonian Gibbs stationary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Hamiltonian.lean#L41-L50
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Hamiltonian.lean#L41-L50

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

theorem QEC.Semantics.Davies.hamiltonianGibbs_stationary (H : Operator V) (hH : H.IsSymmetric)
    (A : κ → Operator V) (hA : ∀ a, (A a).IsSymmetric)
    (rate : κ → HamiltonianFrequency H hH → ℝ) (β : ℝ)
    (hn : ∀ a w, 0 ≤ rate a w)
    (hDB : ∀ a w, rate a (negFrequency (hamiltonianEnergies H hH) w) =
      Real.exp (-β*w.val) * rate a w) :
    hamiltonianDissipator H hH A rate (hamiltonianGibbs H hH β).toOperator = 0 := by sorry
