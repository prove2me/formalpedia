-- Prove2me | Theorems.Thm_QEC_Semantics_norm_normedSpace_exp_le
-- name    : QEC.Semantics.norm_normedSpace_exp_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:39:02.047278+00:00
-- url     : https://prove2.me/theorems/ade888e4-2eaa-4645-a9d8-27c144fa066a
-- title:
--   Semantics: norm normed Space exp le
-- statement:
--   The norm of a Banach-algebra exponential is bounded by the scalar
--   exponential of the norm.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/LieTrotter.lean#L26-L47
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/LieTrotter.lean#L26-L47

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

theorem QEC.Semantics.norm_normedSpace_exp_le (x : A) :
    ‖NormedSpace.exp x‖ ≤ Real.exp ‖x‖ := by sorry
