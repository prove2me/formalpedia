-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_energyProjector_commute
-- name    : QEC.Semantics.Davies.energyProjector_commute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:26:32.639221+00:00
-- url     : https://prove2.me/theorems/9bedf108-f7bd-4996-8522-46b57b3d9472
-- title:
--   Davies: energy Projector commute
-- statement:
--   Commutation with the Hamiltonian means commutation with whole energy spaces,
--   including rotations between basis vectors of a degenerate eigenspace.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L323-L335
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L323-L335

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

theorem QEC.Semantics.Davies.energyProjector_commute (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (A : Operator V) (hA : Commute (diagonal b e) A) (E : ℝ) :
    Commute (energyProjector b e E) A := by sorry
