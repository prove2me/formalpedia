-- Prove2me | Theorems.Thm_Smooth4Algebra_integer_affine_nonnegative
-- name    : Smooth4Algebra.integer_affine_nonnegative
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-06T05:39:25.490345+00:00
-- url     : https://prove2.me/theorems/6ccd0e9f-258e-494a-94c5-7a007462bccf
-- title:
--   An integer-affine function nonnegative everywhere has zero slope
-- statement:
--   Let $a,b\in\mathbb R$. If
--
--   $$a+nb\ge0\qquad\text{for every }n\in\mathbb Z,$$
--
--   then $b=0$.
--
--   This is the elementary all-integer affine-rigidity step used in the norm-invariance discussion. It does not assert the topology, the Laurent factorization, or the Alexander-polynomial theorem.
-- source:
--   Newly authored from cycle7_band_twist_theory.md, norm-invariance/affine nonnegativity discussion; SHA-256 e81d47cad862e6538d0997826a67a43c367fd4096fd62119714e70def075e8b3. This is a new Lean formalization, not an existing source-project theorem split.

import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Real.Basic
set_option autoImplicit false

theorem Smooth4Algebra.integer_affine_nonnegative
    (a b : ℝ) (h : ∀ n : ℤ, 0 ≤ a + (n : ℝ) * b) : b = 0 := by sorry
