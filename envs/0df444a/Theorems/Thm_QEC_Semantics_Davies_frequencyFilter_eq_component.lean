-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_frequencyFilter_eq_component
-- name    : QEC.Semantics.Davies.frequencyFilter_eq_component
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:30:44.213641+00:00
-- url     : https://prove2.me/theorems/1decff94-2507-4782-840a-7c06c44f9e5c
-- title:
--   Davies: frequency Filter eq component
-- statement:
--   Explicit finite interpolation recovers the coherent component, including degeneracies.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/FrequencyLocality.lean#L175-L200
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/FrequencyLocality.lean#L175-L200

import Definitions.Def_QEC_Semantics_Dynamics_Davies_Hamiltonian
import Definitions.Def_QEC_Semantics_Core_SubsystemOperatorAlgebra
import Definitions.Def_QEC_Semantics_Dynamics_Davies_FrequencyLocality
set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.Davies
open Classical
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem QEC.Semantics.Davies.frequencyFilter_eq_component (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (ω : ℝ) (hω : ω ∈ frequencies e) (A : Operator V) :
    frequencyFilter (diagonal b e) ω ((frequencies e).erase ω).toList A =
      frequencyComponent b e A ω := by sorry
