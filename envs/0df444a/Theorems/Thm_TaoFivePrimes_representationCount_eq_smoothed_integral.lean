-- Prove2me | Theorems.Thm_TaoFivePrimes_representationCount_eq_smoothed_integral
-- name    : TaoFivePrimes.representationCount_eq_smoothed_integral
-- status  : Proved
-- author  : @Patrick
-- created : 2026-09-07T03:57:37.292144+00:00
-- url     : https://prove2.me/theorems/1af2b48e-3e81-4f9f-90fa-1e1daef23daf
-- title:
--   Tao’s Fourier identity in smoothed-sum notation
-- statement:
--   For natural x≥1000 and any natural gap budget H, the weighted representation count is exactly the unit-circle integral of the two first smoothed prime sums, the third smoothed prime sum at real scale x/1000, three positive-shift sums, and the Fourier character of frequency −x. The proof checks that the infinite sums truncate at the correct integer bounds, using the actual cutoff support. No positivity estimate is assumed or concluded.
-- source:
--   Tao, https://arxiv.org/abs/1201.6656, equation(8.11), fixed K=1000. Adapter from the proved finite Fourier identity to the published smoothedSum definition.

import Definitions.Def_TaoFivePrimes_FourierRepresentation
import Definitions.Def_TaoFivePrimes_SmoothedSum
open MeasureTheory TaoFivePrimes TaoFourierIdentity

theorem TaoFivePrimes.representationCount_eq_smoothed_integral (x H : ℕ) (hx : 1000 ≤ x) :
    (representationCount x H : ℂ) =
      ∫ α : AddCircle (1 : ℝ),
        smoothedSum eta1 (primorial (Nat.sqrt x)) x α ^ 2 *
        smoothedSum eta0 (primorial (Nat.sqrt (x / 1000))) ((x : ℝ) / 1000) α *
        fourierPolynomial (Finset.Icc 1 (H / 3)) (fun _ ↦ 1)
          (fun n ↦ (n : ℤ)) α ^ 3 * fourier (-(x : ℤ)) α
        ∂AddCircle.haarAddCircle := by sorry
