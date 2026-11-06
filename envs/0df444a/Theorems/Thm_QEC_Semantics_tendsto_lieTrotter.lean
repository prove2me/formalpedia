-- Prove2me | Theorems.Thm_QEC_Semantics_tendsto_lieTrotter
-- name    : QEC.Semantics.tendsto_lieTrotter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:39:20.95511+00:00
-- url     : https://prove2.me/theorems/8c666e3c-f009-4790-814b-1a320a015ed5
-- title:
--   Semantics: tendsto lie Trotter
-- statement:
--   The two-term Lie--Trotter product formula for bounded generators in a
--   complex Banach algebra.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/LieTrotter.lean#L253-L276
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/LieTrotter.lean#L253-L276

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

theorem QEC.Semantics.tendsto_lieTrotter (x y : A) :
    Tendsto
      (fun n : Nat => (lieTrotterStep x y ((n : Complex)⁻¹)) ^ n)
      atTop (nhds (NormedSpace.exp (x + y))) := by sorry
