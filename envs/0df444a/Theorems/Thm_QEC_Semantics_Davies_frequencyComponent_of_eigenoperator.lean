-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_frequencyComponent_of_eigenoperator
-- name    : QEC.Semantics.Davies.frequencyComponent_of_eigenoperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:14:15.892468+00:00
-- url     : https://prove2.me/theorems/6dba73d5-3d8f-4b76-854e-dec143a92a05
-- title:
--   Davies: frequency Component of eigenoperator
-- statement:
--   Spectral uniqueness for any actual eigenoperator, without a chosen common basis.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/FrequencyLocality.lean#L51-L68
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/FrequencyLocality.lean#L51-L68

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

theorem QEC.Semantics.Davies.frequencyComponent_of_eigenoperator (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (A : Operator V) (freq ω : ℝ) (hA : energyDifference (diagonal b e) A = (freq : ℂ) • A) :
    frequencyComponent b e A ω = if freq=ω then A else 0 := by sorry
