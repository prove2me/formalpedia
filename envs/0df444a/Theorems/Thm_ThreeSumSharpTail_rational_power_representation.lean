-- Prove2me | Theorems.Thm_ThreeSumSharpTail_rational_power_representation
-- name    : ThreeSumSharpTail.rational_power_representation
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-13T19:24:41.931444+00:00
-- url     : https://prove2.me/theorems/ef54131f-d900-4e4a-976a-4a0d5a5fbe32
-- title:
--   Finite exponent data and an exact integer-power regime test
-- statement:
--   For rational 0<a<1 and 0<s<1/2 there are natural A,B,c,e with positive denominators, A<=B, 2c<=e, A/B=a and c/e=s/2. For every N,D>=1, D<=N^a holds exactly when D^B<=N^A. This gives finite integer exponent data both for the host parameters and for an exact program branch, without numerical approximation.
-- source:
--   Elementary rational-arithmetic and real-power interface for the finite full-D program realization of the sharp-tail certificate.

import Mathlib

theorem ThreeSumSharpTail.rational_power_representation (a s : ℚ) (ha0 : 0 < a) (ha1 : a < 1)
    (hs0 : 0 < s) (hsHalf : s < 1 / 2) :
    ∃ A B c e : ℕ, 1 ≤ B ∧ 1 ≤ e ∧ A ≤ B ∧ 2 * c ≤ e ∧
      (A : ℝ) / B = (a : ℝ) ∧ (c : ℝ) / e = (s : ℝ) / 2 ∧
      ∀ N D : ℕ, 1 ≤ N → 1 ≤ D →
        ((D : ℝ) ≤ (N : ℝ) ^ (a : ℝ) ↔ D ^ B ≤ N ^ A) := by sorry
