-- Prove2me | Theorems.Thm_Smooth4Algebra_two_cell_phantom_gap
-- name    : Smooth4Algebra.two_cell_phantom_gap
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-06T05:39:17.153968+00:00
-- url     : https://prove2.me/theorems/5bf66c69-6fb6-40ee-a214-1daa6c64f5a6
-- title:
--   Polynomial consequence of two conjugate acyclic cells
-- statement:
--   Let $A,C:\mathbb Z\to\mathbb N$ be finitely supported coefficient sequences with $A\ne0$, and let $g$ be a positive integer. Suppose that for every integer $m$,
--
--   $$A(m)=C(m-1),\qquad C(m)=A\bigl(m-(1-2g)\bigr).$$
--
--   Then $g=1$.
--
--   Equivalently, writing the sequences as Laurent dimension polynomials, the hypotheses are $A=qC$ and $C=q^{1-2g}A$. This is the exact algebraic consequence used for two-cell conjugate phantom rows.
-- source:
--   Newly authored from cycle17_phantom_independent.md, section “Arbitrary-matrix two-cell lemma”, equations (1)–(3) and the finite-support sentence following (3); unpublished local research note, no public URL. SHA-256 f9d2af34ac68d1728b6386e624221f43a9eccffe678f50af3103f1b8c1cbbf92.

import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Int.Basic
set_option autoImplicit false

theorem Smooth4Algebra.two_cell_phantom_gap
    (A C : ℤ →₀ ℕ) (hA : A ≠ 0)
    (gap : ℤ) (h_gap : 0 < gap)
    (h_forward : ∀ m : ℤ, A m = C (m - 1))
    (h_conjugate : ∀ m : ℤ, C m = A (m - (1 - 2 * gap))) :
    gap = 1 := by sorry
