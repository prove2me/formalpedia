-- Prove2me | Theorems.Thm_QEC_Semantics_tendsto_lieTrotter_localError
-- name    : QEC.Semantics.tendsto_lieTrotter_localError
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:39:16.581205+00:00
-- url     : https://prove2.me/theorems/7d3e1808-0613-452b-aeef-3d071d22c367
-- title:
--   Semantics: tendsto lie Trotter local Error
-- statement:
--   The one-step Trotter defect is little-o of the step size.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/LieTrotter.lean#L109-L125
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/LieTrotter.lean#L109-L125

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Definitions.Def_QEC_Semantics_Dynamics_LieTrotter
set_option autoImplicit false
open QEC QEC.Semantics
open Filter
open scoped Topology
noncomputable section
variable {A : Type*} [NormedRing A] [NormOneClass A]
  [NormedAlgebra Complex A] [CompleteSpace A]

theorem QEC.Semantics.tendsto_lieTrotter_localError (x y : A) :
    Tendsto
      (fun n : Nat => (n : Real) *
        ‖NormedSpace.exp (((n : Complex)⁻¹) • (x + y)) -
          lieTrotterStep x y ((n : Complex)⁻¹)‖)
      atTop (nhds 0) := by sorry
