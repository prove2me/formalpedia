-- Prove2me | Theorems.Thm_QAOAE3Lin2_General_eq_39
-- name    : QAOAE3Lin2.General.eq_39
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:02:25.273775+00:00
-- url     : https://prove2.me/theorems/3c66c48a-55ec-4fdd-b225-fc6d86e31e21
-- title:
--   Section II, (39), p. 8 — max_r |x_r + a₂x_r² + … + a_kx_r^k| ≥ 1/k at x_r = cos(πr/k), k odd
-- statement:
--   Let $k$ be an odd positive integer and $x_r=\cos(\pi r/k)$ for $r=0,1,\dots,k$. For all real $a_2,\dots,a_k$,
--   $$\max_{r=0,1,\dots,k}\big|x_r+a_2x_r^2+\dots+a_kx_r^k\big|\ge\frac1k .$$
--
--   A polynomial with linear coefficient $1$ cannot be uniformly small on the $k+1$ Chebyshev extreme points. The paper cites it as Corollary 2.7 of Dinur–Friedgut–Kindler–O'Donnell and uses it to find a grid angle where the main term of (37) is large.
--
--   **Formalization Note.** The maximum over a finite set is stated as the existence of an $r\in\{0,\dots,k\}$ attaining the bound. Both the absolute value and the oddness of $k$ are essential: for even $k=6$ the statement is false.
-- source:
--   Farhi, Goldstone, Gutmann, A Quantum Approximate Optimization Algorithm Applied to a Bounded Occurrence Constraint Problem, arXiv:1412.6062v2, p. 8, Section II, (39) (citing Dinur, Friedgut, Kindler, O'Donnell, Corollary 2.7)

import Mathlib
import Definitions.Def_QAOAE3Lin2_General_Setting

namespace QAOAE3Lin2.General

theorem eq_39 (k : ℕ) (hk : Odd k) (a : ℕ → ℝ) :
    ∃ r ∈ Finset.range (k + 1), 1 / (k : ℝ) ≤
      |Real.cos (Real.pi * r / k) + ∑ j ∈ Finset.Icc 2 k, a j * Real.cos (Real.pi * r / k) ^ j| := by sorry

end QAOAE3Lin2.General
