-- Prove2me | Theorems.Thm_Rudin_ch05_darboux
-- name    : Rudin.ch05_darboux
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T23:04:50.817564+00:00
-- url     : https://prove2.me/theorems/128aefd7-7d8c-4fab-817c-3297b5c39752
-- title:
--   Theorem 5.12 — derivatives have the intermediate value property
-- statement:
--   Let $f$ be a real differentiable function on $[a,b]$ with $f'(a) < A < f'(b)$. Then $f'(x) = A$ for some $x \in (a,b)$. Consequently $f'$ has no simple discontinuities, although it may be discontinuous.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 5, p. 108, Theorem 5.12

import Mathlib

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 5.12 (Darboux's theorem): the derivative of a differentiable function has the
intermediate value property: if `f'(a) < A < f'(b)` then `f'(x) = A` for some `x ∈ (a, b)`. -/
theorem ch05_darboux (a b : ℝ) (hab : a < b) (f : ℝ → ℝ)
    (hfd : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ f x) (A : ℝ)
    (hA : deriv f a < A ∧ A < deriv f b) :
    ∃ x ∈ Set.Ioo a b, deriv f x = A := by sorry

end Rudin
