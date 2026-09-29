-- Prove2me | Theorems.Thm_TaoFivePrimes_integer_hilbert_sum_bound
-- name    : TaoFivePrimes.integer_hilbert_sum_bound
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-12T16:50:21.965392+00:00
-- url     : https://prove2.me/theorems/16161f30-78e9-4015-90f7-d191d003f4ed
-- title:
--   Integer-grid Hilbert inequality with constant 7/2
-- statement:
--   Let I be a finite index set, let k : I → ℤ be injective, and let z : I → ℂ. Then
--
--   $$\left|\sum_{m\in I}\sum_{n\ne m}\frac{\overline{z_m}z_n}{k_m-k_n}\right|\le\frac72\sum_{m\in I}|z_m|^2.$$
--
--   This is an auxiliary integer-grid estimate for a proposed Type II sine-kernel argument in the unit-numerator case of Tao Theorem 5.1. The constant is not asserted to be sharp. This result alone does not establish the finite large-sieve estimate or Tao Theorem 5.1.
-- source:
--   Derived integer-grid corollary of the finite Hilbert eigen-identity Zeta23.MV.eigen_identityPrime, platform theorem 32ec0da9-b9af-40b5-a23f-66e884bd5f50, accepted proof e2c521f7-2d40-47aa-84b0-cd6cdb3872a6. Source: https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/MV/EigenIdentity.lean . The integer-grid specialization and 7/2 constant are derived here, not quoted as a statement from Tao.

import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Field
open Finset

theorem TaoFivePrimes.integer_hilbert_sum_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (idx : ι → ℤ) (hinj : Function.Injective idx) (x : ι → ℂ) :
    ‖∑ m, ∑ n ∈ univ.erase m,
      star (x m) * ((1 / ((idx m : ℝ) - (idx n : ℝ)) : ℝ) : ℂ) * x n‖ ≤
        (7 / 2 : ℝ) * ∑ i, ‖x i‖ ^ 2 := by sorry
