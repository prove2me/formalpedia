-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_frequencyComponent_zero_eq_pinching
-- name    : QEC.Semantics.Davies.frequencyComponent_zero_eq_pinching
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:28:15.944924+00:00
-- url     : https://prove2.me/theorems/f0fd6c62-bc8b-41db-850e-1060fd7edc2a
-- title:
--   Davies: frequency Component zero eq pinching
-- statement:
--   Zero-frequency extraction is the sum of compressions to full energy spaces.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Pinching.lean#L16-L23
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Pinching.lean#L16-L23

import Definitions.Def_QEC_Semantics_Dynamics_Davies_Spectral
import Definitions.Def_QEC_Semantics_Dynamics_Davies_TraceBound
import Definitions.Def_QEC_Semantics_Dynamics_Davies_Pinching
set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.Davies
open Classical
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem QEC.Semantics.Davies.frequencyComponent_zero_eq_pinching (b : OrthonormalBasis ι ℂ V)
    (e : ι → ℝ) (A : Operator V) :
    frequencyComponent b e A 0 = ∑ E ∈ energyValues e,
      energyProjector b e E * A * energyProjector b e E := by sorry
