-- Prove2me | Theorems.Thm_Smooth4Laurent_mass_three_sharpness
-- name    : Smooth4Laurent.mass_three_sharpness
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-06T05:40:17.074568+00:00
-- url     : https://prove2.me/theorems/d0385d13-50f8-4ebd-bf1c-320f957fc88b
-- title:
--   A sharp mass-three counterexample
-- statement:
--   The Laurent polynomial W(q)=1+q−q²+q³+q⁴ has signed coefficient sum3 and coefficient−1 at exponent2, while both (1+q)W and (1+q²)W have nonnegative coefficients at every integer exponent.
-- source:
--   Ryan Shin research workspace, unpublished cycle9_positive_quotient_lemma.md (2026), section1, Integer Laurent positivity. Source SHA-256 73cb004e73b4f14e8a2a4bc5f1c4b345f69c8390f060a76e284b5d44b1d6a925. No public URL. These are newly authored coefficient-function interfaces to the manuscript statements.

import Mathlib

set_option autoImplicit false

/-- The explicit sharp mass-three Laurent polynomial is 1+q-q²+q³+q⁴. -/

theorem Smooth4Laurent.mass_three_sharpness :
    let w : ℤ →₀ ℤ := Finsupp.single 0 1 + Finsupp.single 1 1 -
      Finsupp.single 2 1 + Finsupp.single 3 1 + Finsupp.single 4 1
    (∀ j : ℤ, 0 ≤ w j + w (j - 1)) ∧
      (∀ j : ℤ, 0 ≤ w j + w (j - 2)) ∧
      w.sum (fun _ a => a) = 3 ∧ w 2 = -1 := by
  sorry
