-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_energyProjector_apply_eigenvector
-- name    : QEC.Semantics.Davies.energyProjector_apply_eigenvector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:04:03.239691+00:00
-- url     : https://prove2.me/theorems/7e948352-98ca-434f-b32a-9baa4c7eb388
-- title:
--   Davies: energy Projector apply eigenvector
-- statement:
--   Every vector of an eigenspace, not only selected basis vectors, has the
--   expected energy-projector action.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L397-L418
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L397-L418

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

theorem QEC.Semantics.Davies.energyProjector_apply_eigenvector (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (x : V) (lam E : ℝ) (hx : diagonal b e x = (lam : ℂ) • x) :
    energyProjector b e E x = if lam = E then x else 0 := by sorry
