-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_weightedJump_protected
-- name    : QEC.Semantics.Davies.weightedJump_protected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:29:03.19944+00:00
-- url     : https://prove2.me/theorems/32f96031-1071-4623-9bea-c9dc71114287
-- title:
--   Davies: weighted Jump protected
-- statement:
--   Coupling protection plus Hamiltonian commutation supplies the existing
--   operator-valued protected-jump predicate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Stationarity.lean#L217-L225
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Stationarity.lean#L217-L225

import Definitions.Def_QEC_Semantics_Dynamics_Davies_Spectral
import Definitions.Def_QEC_Semantics_Dynamics_Davies_Stationarity
set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.Davies
open Classical ThermalEncoding
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V]
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem QEC.Semantics.Davies.weightedJump_protected {κ : Type*} [Fintype κ] (b : OrthonormalBasis ι ℂ V)
    (e : ι → ℝ) (A : κ → Operator V) (rate : κ → Frequency e → ℝ)
    (O P : Operator V) (hO : Commute (diagonal b e) O) (hP : Commute (diagonal b e) P)
    (h : ∀ a, (A a * O - O * A a) * P = 0) :
    JumpProtected (weightedJump b e A rate) O P := by sorry
