-- Prove2me | Theorems.Thm_TaoFivePrimes_finite_fourier_polynomial_parseval
-- name    : TaoFivePrimes.finite_fourier_polynomial_parseval
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-25T21:38:50.601478+00:00
-- url     : https://prove2.me/theorems/8bf839f6-085f-4817-849e-86f73a845256
-- title:
--   Parseval for a finite Fourier polynomial
-- statement:
--   For real coefficients c_0,...,c_M, let P(?)=?_{k=0}^M c_k e^{2?ik?}. The normalized squared L2 norm of P on the unit circle is ?_{k=0}^M c_k�.
-- source:
--   Mathlib.Analysis.Fourier.AddCircle: orthonormality of Fourier characters; finite-dimensional Parseval identity

import Mathlib.Analysis.Fourier.AddCircle
open MeasureTheory

namespace TaoFivePrimes
theorem finite_fourier_polynomial_parseval (M : Nat) (c : Nat -> Real) :
    MeasureTheory.integral AddCircle.haarAddCircle
      (fun alpha : AddCircle (1 : Real) =>
        norm (Finset.sum (Finset.range (M + 1))
          (fun k => (c k : Complex) * fourier (k : Int) alpha)) ^ 2) =
      Finset.sum (Finset.range (M + 1)) (fun k => (c k) ^ 2) := by
  sorry
end TaoFivePrimes
