-- Prove2me | Theorems.Thm_RovelliLQG_area_gap
-- name    : RovelliLQG.area_gap
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T19:29:12.295987+00:00
-- url     : https://prove2.me/theorems/dfd5ae91-78dd-4ad7-8328-8ca36cccc674
-- title:
--   Eq. (13): the area gap $\sqrt{\tfrac12(\tfrac12+1)}=\tfrac{\sqrt3}{2}$
-- statement:
--   For a spin $j\in\{0,\tfrac12,1,\tfrac32,\dots\}$ let $\sqrt{j(j+1)}$ be the square root of the $SU(2)$ Casimir eigenvalue. The smallest non-vanishing such value is attained at $j=\tfrac12$:
--   $$\min\Big\{\sqrt{j(j+1)}:\ j\in\{\tfrac12,1,\tfrac32,\dots\}\Big\}=\sqrt{\tfrac12\big(\tfrac12+1\big)}=\frac{\sqrt3}{2}.$$
--
--   This is the review's **area gap** (eq. (13)): the lowest nonzero area eigenvalue in dimensionless units, "directly responsible for the ultraviolet finiteness of the theory".
--
--   **Formalization Note** Spins are written $j=k/2$ with $k\in\mathbb N$, $k\neq0$; the statement is that $\sqrt3/2$ is the least element of the set of values.
-- source:
--   C. Rovelli, Loop quantum gravity: the first 25 years, Class. Quantum Grav. 28 (2011) 153002, doi:10.1088/0264-9381/28/15/153002, arXiv:1012.4707, §2.1, p. 5, eq. (13)

import Mathlib
import Definitions.Def_RovelliLQG_Defs

open scoped InnerProductSpace

namespace RovelliLQG

theorem area_gap :
    IsLeast {a : ℝ | ∃ k : ℕ, k ≠ 0 ∧ a = casimirRoot ((k : ℝ) / 2)} (Real.sqrt 3 / 2) := by
  sorry

end RovelliLQG
