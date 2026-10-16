-- Prove2me | Theorems.Thm_Real_exists_finite_moment_weights
-- name    : Real.exists_finite_moment_weights
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T09:11:06.587673+00:00
-- url     : https://prove2.me/theorems/7541bc52-f001-4608-9d98-db8a5c449dd0
-- title:
--   Finite distinct nodes reproduce polynomial moments at any point
-- statement:
--   Let $v_0,\ldots,v_{N-1}$ be distinct real numbers, and let $a\in\mathbb R$. There are real weights $c_j$ such that
--   $$\sum_{j=0}^{N-1}c_jv_j^r=a^r\qquad(0\le r<N).$$
--   Thus weighted evaluation at the nodes reproduces evaluation at $a$ for every polynomial of degree less than $N$. The weights need not be nonnegative. The empty case $N=0$ is allowed. This follows by solving the transpose Vandermonde system. For boundary extension, take negative nodes and $a=1$ to match finitely many normal derivatives.
-- source:
--   Sung-Jin Oh, Lecture Notes for Math 222A, March 19, 2024, proof of Proposition 11.13, Step 2, printed p. 158, equations (11.3)-(11.4), https://math.berkeley.edu/~sjoh/pdfs/notes-math222a.pdf . Generalization of the finite Vandermonde system there from a constant right-hand side to evaluation at an arbitrary point.

import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Real.Basic
set_option autoImplicit false

theorem Real.exists_finite_moment_weights (N : ℕ) (v : Fin N → ℝ) (hv : Function.Injective v) (a : ℝ) :
    ∃ c : Fin N → ℝ, ∀ r : Fin N, ∑ j : Fin N, c j * v j ^ (r : ℕ) = a ^ (r : ℕ) := by sorry
