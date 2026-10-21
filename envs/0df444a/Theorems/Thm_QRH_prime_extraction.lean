-- Prove2me | Theorems.Thm_QRH_prime_extraction
-- name    : QRH.prime_extraction
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-20T12:50:07.926033+00:00
-- url     : https://prove2.me/theorems/50e95a48-1077-4d39-873c-d41bd568099c
-- title:
--   The power saving for A_1(D) from the mean square over sixth-power rows
-- statement:
--   Assume the coefficient sequence is bounded by one on the elements prime to S, and the mean-square estimate: there is k with msSum over the rows of norm at most D^(1+theta) bounded by k D^(2+theta+eps) for all D >= 2. Then there is k with |A_1(D)| <= k D^(11/12 + 5 theta / 12 + eps) for all D >= 2. The extraction averages the mean square over the rows u = p^6: the sixth-power identity chi_n(p^6) = 1 when p does not divide n makes A_{p^6}(D) equal A_1(D) up to the terms divisible by p, which the divisor-count bound controls; Landau's prime ideal theorem supplies on the order of Y / log Y rows with Y = D^((1+theta)/6), and their sixth powers are distinct.
-- source:
--   The Quasi-Riemann Hypothesis, October 2026, Section 3 (equation 3.4, the prime-extraction step).

import Mathlib
import Definitions.Def_QRH_arith
import Definitions.Def_QRH_sums
import Definitions.Def_QRH_lfun

universe u

namespace QRH

/-- The prime-extraction step of section 3 of the source: the power
saving for the smoothed Möbius sums A₁(D) follows from the mean-square
estimate for the family. For the rows u = p⁶ with p a primary prime of
norm in (Y/2, Y], the identity χ_n(p⁶) = 1_{p ∤ n} makes A_{p⁶}(D) equal
A₁(D) up to the terms divisible by p, which the divisor-count bound of
the interface controls by D / N p; Landau's prime ideal theorem supplies
≍ Y / log Y such primes, and their sixth powers are distinct rows of
norm at most D^(1+θ) with Y = D^((1+θ)/6). Averaging the mean square
over these rows bounds |A₁(D)|² by D^(11/6+5θ/6+ε), that is, |A₁(D)| by
D^(11/12+5θ/12+ε). -/
theorem prime_extraction (W : QRHWorld.{u}) (S : QRHSums W)
    (c : W.E → ℂ) (Wt : ℝ → ℂ)
    (hcb : ∀ n : W.E, W.Sgood n → ‖c n‖ ≤ 1)
    (θ ε : ℝ) (hθ : 0 < θ) (hθ₁ : θ ≤ 1 / 10) (hε : 0 < ε)
    (hms : ∃ k : ℝ, ∀ D : ℝ, 2 ≤ D →
      msSum W S c Wt (D ^ (1 + θ)) D (2 * D) ≤ k * D ^ (2 + θ + ε)) :
    ∃ k : ℝ, ∀ D : ℝ, 2 ≤ D →
      ‖A1sum W S c Wt D (2 * D)‖
        ≤ k * D ^ (11 / 12 + 5 * θ / 12 + ε) := by
  sorry

end QRH
