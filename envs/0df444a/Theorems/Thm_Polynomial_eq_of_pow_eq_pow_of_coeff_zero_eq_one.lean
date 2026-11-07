-- Prove2me | Theorems.Thm_Polynomial_eq_of_pow_eq_pow_of_coeff_zero_eq_one
-- name    : Polynomial.eq_of_pow_eq_pow_of_coeff_zero_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:30:50.197379+00:00
-- url     : https://prove2.me/theorems/eb8ab63b-215a-4e81-9ffd-f0b7f42c9d00
-- title:
--   Polynomial: eq of pow eq pow of coeff zero eq one
-- statement:
--   A polynomial with constant coefficient one has at most one normalized
--   `n`-th root when `n` is nonzero in the coefficient domain.  The normalization
--   removes the usual root-of-unity ambiguity: in the factorization of
--   `f ^ n - g ^ n`, the complementary factor has constant coefficient `n`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Algebra/MatrixAlgebraNorm.lean#L25-L53
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Algebra/MatrixAlgebraNorm.lean#L25-L53

import Mathlib.RingTheory.Norm.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.Tactic.NoncommRing
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Algebra_MatrixAlgebraNorm
set_option autoImplicit false
open scoped Matrix
open Polynomial

theorem Polynomial.eq_of_pow_eq_pow_of_coeff_zero_eq_one
    {R : Type*} [CommRing R]
    {f g : R[X]} {n : ℕ}
    (hn : IsUnit (n : R))
    (hf : f.coeff 0 = 1) (hg : g.coeff 0 = 1)
    (hpow : f ^ n = g ^ n) :
    f = g := by sorry
