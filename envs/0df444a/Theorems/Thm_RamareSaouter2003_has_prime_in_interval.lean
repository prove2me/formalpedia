-- Prove2me | Theorems.Thm_RamareSaouter2003_has_prime_in_interval
-- name    : RamareSaouter2003.has_prime_in_interval
-- status  : Open
-- author  : @marwahaha
-- created : 2026-09-09T07:56:37.689952+00:00
-- url     : https://prove2.me/theorems/3a85680d-cea1-4235-898e-7419c521bb84
-- title:
--   Ramaré–Saouter 2003 exact short-prime interval
-- statement:
--   For every real number $x>10{,}726{,}905{,}041$, the half-open interval
--
--   $$
--   \left(x\left(1-\frac{1}{28{,}314{,}000}\right),x\right]
--   $$
--
--   contains a prime.
--
--   This is the exact explicit short-interval result used to obtain the rounded prime-gap input in Tao's five-primes argument.
--
--   **Formalization Note** The existential prime is represented by a natural number, with strict membership at the lower endpoint and non-strict membership at the upper endpoint.
-- source:
--   Olivier Ramaré and Yannick Saouter, “Short effective intervals containing primes,” Journal of Number Theory 98 (2003), no. 1, 10–33, Theorem 3 on printed p. 13, DOI: https://doi.org/10.1016/S0022-314X(02)00029-X. Also formalized under the same declaration name in PrimeNumberTheoremAnd/IEANTN/TMEEMT.lean at commit a5154676af9aa3095150ee410cdda80555aa0642: https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/a5154676af9aa3095150ee410cdda80555aa0642/PrimeNumberTheoremAnd/IEANTN/TMEEMT.lean

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic

namespace RamareSaouter2003

theorem has_prime_in_interval (x : ℝ) (hx : 10726905041 < x) :
    ∃ p : ℕ, p.Prime ∧ x * (1 - 1 / 28314000) < (p : ℝ) ∧ (p : ℝ) ≤ x := by
  sorry

end RamareSaouter2003
