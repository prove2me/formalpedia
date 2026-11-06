-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_sum_frequency_adjoint_square
-- name    : QEC.Semantics.Davies.sum_frequency_adjoint_square
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:28:18.005197+00:00
-- url     : https://prove2.me/theorems/61c5b6f1-4570-4ae7-865f-07155ed5d7de
-- title:
--   Davies: sum frequency adjoint square
-- statement:
--   Cross terms between different output energies disappear, while terms inside
--   a degenerate output energy remain together.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Pinching.lean#L41-L68
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Pinching.lean#L41-L68

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

theorem QEC.Semantics.Davies.sum_frequency_adjoint_square (b : OrthonormalBasis ι ℂ V)
    (e : ι → ℝ) (A : Operator V) :
    (∑ ω : Frequency e, LinearMap.adjoint (frequencyComponent b e A ω.val) *
      frequencyComponent b e A ω.val) =
      frequencyComponent b e (LinearMap.adjoint A * A) 0 := by sorry
