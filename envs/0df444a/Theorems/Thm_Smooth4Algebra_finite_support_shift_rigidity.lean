-- Prove2me | Theorems.Thm_Smooth4Algebra_finite_support_shift_rigidity
-- name    : Smooth4Algebra.finite_support_shift_rigidity
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-06T05:39:08.871735+00:00
-- url     : https://prove2.me/theorems/e496ea94-1016-4441-9e06-5ce791244915
-- title:
--   A nonzero finitely supported sequence has no nonzero period
-- statement:
--   Let $R$ be any type with a distinguished zero, and let $f:\mathbb Z\to R$ have finite support and be nonzero. If an integer $k$ satisfies
--
--   $$f(m+k)=f(m)\qquad\text{for every }m\in\mathbb Z,$$
--
--   then $k=0$.
--
--   The result requires no order, addition, multiplication, positivity or cancellation law on the coefficient type. It records the finite-support rigidity used for Laurent dimension polynomials.
-- source:
--   Newly authored from cycle17_phantom_independent.md, section “Arbitrary-matrix two-cell lemma”, equations (1)–(3) and the finite-support sentence following (3); unpublished local research note, no public URL. SHA-256 f9d2af34ac68d1728b6386e624221f43a9eccffe678f50af3103f1b8c1cbbf92.

import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Int.Basic
set_option autoImplicit false

theorem Smooth4Algebra.finite_support_shift_rigidity
    {R : Type*} [Zero R] (f : ℤ →₀ R) (hf : f ≠ 0)
    (k : ℤ) (h_shift : ∀ m : ℤ, f (m + k) = f m) : k = 0 := by sorry
