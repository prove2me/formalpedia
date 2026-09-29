-- Prove2me | Theorems.Thm_TaoFivePrimes_finite_fourier_product_convolution
-- name    : TaoFivePrimes.finite_fourier_product_convolution
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-25T21:38:50.448705+00:00
-- url     : https://prove2.me/theorems/08d992ad-fc39-4ef3-b8df-c7d22040486f
-- title:
--   Convolution formula for finite Fourier products
-- statement:
--   Let A(?)=?_{n=0}^x a_n e^{2?in?} and B(?)=?_{j=1}^N b_j e^{2?ij?}. Their product has coefficient ?_{n+j=k}a_n b_j at frequency k.
-- source:
--   Finite Fourier multiplication formula; frequencies in the ranges 0 through x and 1 through N

import Mathlib.Analysis.Fourier.AddCircle
open MeasureTheory

namespace TaoFivePrimes
theorem finite_fourier_product_convolution (x N : Nat) (a b : Nat -> Real)
    (alpha : AddCircle (1 : Real)) :
    (Finset.sum (Finset.range (x + 1))
      (fun n => (a n : Complex) * fourier (n : Int) alpha)) *
      (Finset.sum (Finset.Icc 1 N)
        (fun j => (b j : Complex) * fourier (j : Int) alpha)) =
    Finset.sum (Finset.range (x + N + 1)) (fun k =>
      ((Finset.sum (Finset.range (x + 1)) (fun n =>
        Finset.sum (Finset.Icc 1 N) (fun j =>
          if k = n + j then a n * b j else 0)) : Real) : Complex) *
        fourier (k : Int) alpha) := by
  sorry
end TaoFivePrimes
