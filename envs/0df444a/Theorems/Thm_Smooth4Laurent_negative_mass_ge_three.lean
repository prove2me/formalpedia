-- Prove2me | Theorems.Thm_Smooth4Laurent_negative_mass_ge_three
-- name    : Smooth4Laurent.negative_mass_ge_three
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-06T05:39:45.306324+00:00
-- url     : https://prove2.me/theorems/2d22450e-c4ce-4a0c-8829-b51d65e80eb5
-- title:
--   A negative Laurent coefficient forces total mass at least three
-- statement:
--   Let W(q)=∑ wⱼqʲ be an integer Laurent polynomial with finite support. Suppose wⱼ+wⱼ₋₁≥0 and wⱼ+wⱼ₋₂≥0 for every integer j, equivalently (1+q)W and (1+q²)W are coefficientwise nonnegative. If any coefficient of W is negative, then the signed coefficient sum W(1) is at least3.
-- source:
--   Ryan Shin research workspace, unpublished cycle9_positive_quotient_lemma.md (2026), section1, Integer Laurent positivity. Source SHA-256 73cb004e73b4f14e8a2a4bc5f1c4b345f69c8390f060a76e284b5d44b1d6a925. No public URL. These are newly authored coefficient-function interfaces to the manuscript statements.

import Mathlib

set_option autoImplicit false

/-- The integer-coefficient, finite-support positivity threshold from Cycle9 §1. -/

theorem Smooth4Laurent.negative_mass_ge_three
    (w : ℤ →₀ ℤ)
    (hOne : ∀ j : ℤ, 0 ≤ w j + w (j - 1))
    (hTwo : ∀ j : ℤ, 0 ≤ w j + w (j - 2))
    (hNegative : ∃ j : ℤ, w j < 0) :
    3 ≤ w.sum (fun _ a => a) := by
  sorry
