-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_frequencyComponent_protected
-- name    : QEC.Semantics.Davies.frequencyComponent_protected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:26:38.27895+00:00
-- url     : https://prove2.me/theorems/8de4a434-6882-433e-bca7-7dbd325cd715
-- title:
--   Davies: frequency Component protected
-- statement:
--   Protection transfers through grouped frequency extraction without selecting
--   rank-one projectors inside a degenerate eigenspace.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L354-L362
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L354-L362

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

theorem QEC.Semantics.Davies.frequencyComponent_protected (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (A O P : Operator V) (hO : Commute (diagonal b e) O)
    (hP : Commute (diagonal b e) P) (h : (A * O - O * A) * P = 0) (ω : ℝ) :
    (frequencyComponent b e A ω * O - O * frequencyComponent b e A ω) * P = 0 := by sorry
