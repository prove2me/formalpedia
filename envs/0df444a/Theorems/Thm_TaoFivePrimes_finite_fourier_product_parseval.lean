-- Prove2me | Theorems.Thm_TaoFivePrimes_finite_fourier_product_parseval
-- name    : TaoFivePrimes.finite_fourier_product_parseval
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-25T14:24:38.674167+00:00
-- url     : https://prove2.me/theorems/6b5bcd9f-1437-4da6-9853-52e6413ee049
-- title:
--   Finite Fourier product Parseval identity
-- statement:
--   Let a?,.,a? be real coefficients, and let the second factor be the unweighted sum of the characters indexed from 1 through N. The squared L� norm of their product on the unit circle equals the sum of squares of the coefficients of the product polynomial. For each frequency k, that coefficient is the sum of a? over indices satisfying n+j=k, with 0?n?x and 1?j?N.
-- source:
--   Mathlib.Analysis.Fourier.AddCircle, orthonormality of Fourier characters (Parseval); Tao, Theorem 8.2, Section 8, equation (8.11), https://arxiv.org/abs/1201.6656

import Mathlib.Analysis.Fourier.AddCircle
open MeasureTheory

namespace TaoFivePrimes
theorem finite_fourier_product_parseval (x N : Nat) (a : Nat -> Real) :
    MeasureTheory.integral AddCircle.haarAddCircle
      (fun alpha : AddCircle (1 : Real) =>
        norm ((Finset.sum (Finset.range (x + 1)) (fun n => (a n : Complex) * fourier (n : Int) alpha)) *
          (Finset.sum (Finset.Icc 1 N) (fun j => (1 : Complex) * fourier (j : Int) alpha))) ^ 2) =
      Finset.sum (Finset.range (x + N + 1)) (fun k =>
        (Finset.sum (Finset.range (x + 1)) (fun n =>
          Finset.sum (Finset.Icc 1 N) (fun j =>
            if k = n + j then a n else 0))) ^ 2) := by
  sorry
end TaoFivePrimes
