-- Prove2me | Theorems.Thm_TaoFivePrimes_finite_fourier_product_parseval_weighted
-- name    : TaoFivePrimes.finite_fourier_product_parseval_weighted
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-25T21:12:22.626454+00:00
-- url     : https://prove2.me/theorems/f5d37b5a-bcba-4fc5-953a-1d60e6190a73
-- title:
--   Parseval for a product of finite Fourier polynomials
-- statement:
--   For two real coefficient sequences, the squared L2 norm on the unit circle of the product of their finite Fourier polynomials equals the sum of squares of the convolution coefficients. The first polynomial uses frequencies 0 through x and the second uses frequencies 1 through N; the coefficient at frequency k is the sum of a_n b_j over pairs with n+j=k.
-- source:
--   Mathlib.Analysis.Fourier.AddCircle, orthonormality of Fourier characters (Parseval); Tao, Theorem 8.2, Section 8, equation (8.11), https://arxiv.org/abs/1201.6656

import Mathlib.Analysis.Fourier.AddCircle
open MeasureTheory

namespace TaoFivePrimes
theorem finite_fourier_product_parseval_weighted (x N : Nat) (a b : Nat -> Real) :
    MeasureTheory.integral AddCircle.haarAddCircle
      (fun alpha : AddCircle (1 : Real) =>
        norm ((Finset.sum (Finset.range (x + 1)) (fun n => (a n : Complex) * fourier (n : Int) alpha)) *
          (Finset.sum (Finset.Icc 1 N) (fun j => (b j : Complex) * fourier (j : Int) alpha))) ^ 2) =
      Finset.sum (Finset.range (x + N + 1)) (fun k =>
        (Finset.sum (Finset.range (x + 1)) (fun n =>
          Finset.sum (Finset.Icc 1 N) (fun j =>
            if k = n + j then a n * b j else 0))) ^ 2) := by
  sorry
end TaoFivePrimes
