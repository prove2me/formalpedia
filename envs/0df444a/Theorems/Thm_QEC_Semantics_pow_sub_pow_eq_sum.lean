-- Prove2me | Theorems.Thm_QEC_Semantics_pow_sub_pow_eq_sum
-- name    : QEC.Semantics.pow_sub_pow_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:39:10.249869+00:00
-- url     : https://prove2.me/theorems/517d70f1-2f15-4755-8ac6-0745dccaae29
-- title:
--   Semantics: pow sub pow eq sum
-- statement:
--   A noncommutative telescoping expansion for the difference of two powers.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/LieTrotter.lean#L50-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/LieTrotter.lean#L50-L74

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

theorem QEC.Semantics.pow_sub_pow_eq_sum (x y : A) (n : Nat) :
    x ^ n - y ^ n =
      ∑ k ∈ Finset.range n, x ^ k * (x - y) * y ^ (n - 1 - k) := by sorry
