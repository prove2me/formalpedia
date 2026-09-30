-- Prove2me | Theorems.Thm_Smooth4Laurent_mass_two_positive
-- name    : Smooth4Laurent.mass_two_positive
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-06T05:39:59.937394+00:00
-- url     : https://prove2.me/theorems/988bc029-7a8a-43d7-9413-9e9cc3f86c24
-- title:
--   Mass-two positivity from two positive Laurent products
-- statement:
--   Let W(q)=∑ wⱼqʲ have integer coefficients and finite support. If (1+q)W and (1+q²)W are coefficientwise nonnegative and the signed sum W(1)=2, then every coefficient of W is nonnegative. Negative exponents are allowed and no degree or support-width bound is imposed.
-- source:
--   Ryan Shin research workspace, unpublished cycle9_positive_quotient_lemma.md (2026), section1, Integer Laurent positivity. Source SHA-256 73cb004e73b4f14e8a2a4bc5f1c4b345f69c8390f060a76e284b5d44b1d6a925. No public URL. These are newly authored coefficient-function interfaces to the manuscript statements.

import Mathlib

set_option autoImplicit false

/-- Mass two forces positivity when both specified Laurent products are positive. -/

theorem Smooth4Laurent.mass_two_positive
    (w : ℤ →₀ ℤ)
    (hOne : ∀ j : ℤ, 0 ≤ w j + w (j - 1))
    (hTwo : ∀ j : ℤ, 0 ≤ w j + w (j - 2))
    (hMass : w.sum (fun _ a => a) = 2) :
    ∀ j : ℤ, 0 ≤ w j := by
  sorry
