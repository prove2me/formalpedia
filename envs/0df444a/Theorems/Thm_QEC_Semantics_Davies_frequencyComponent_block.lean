-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_frequencyComponent_block
-- name    : QEC.Semantics.Davies.frequencyComponent_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:27:30.052254+00:00
-- url     : https://prove2.me/theorems/8c864acd-c141-4e1b-a542-a71f8768b49d
-- title:
--   Davies: frequency Component block
-- statement:
--   The exact grouped spectral-block characterization.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L467-L475
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L467-L475

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

theorem QEC.Semantics.Davies.frequencyComponent_block (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (A : Operator V) (E F ω : ℝ) :
    energyProjector b e E * frequencyComponent b e A ω * energyProjector b e F =
      if F-E = ω then energyProjector b e E * A * energyProjector b e F else 0 := by sorry
