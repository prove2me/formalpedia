-- Prove2me | Theorems.Thm_QEC_Semantics_norm_pow_sub_pow_le
-- name    : QEC.Semantics.norm_pow_sub_pow_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:39:09.725041+00:00
-- url     : https://prove2.me/theorems/9fa69dfc-6764-4d24-8d5f-235f2382974a
-- title:
--   Semantics: norm pow sub pow le
-- statement:
--   Norm estimate associated with `pow_sub_pow_eq_sum`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/LieTrotter.lean#L77-L93
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/LieTrotter.lean#L77-L93

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

theorem QEC.Semantics.norm_pow_sub_pow_le (x y : A) (n : Nat) :
    ‖x ^ n - y ^ n‖ ≤
      ∑ k ∈ Finset.range n,
        ‖x‖ ^ k * ‖x - y‖ * ‖y‖ ^ (n - 1 - k) := by sorry
