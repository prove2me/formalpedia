-- Prove2me | Theorems.Thm_PolyhedralSOC_UpperBound_planar_approx_extend
-- name    : PolyhedralSOC.UpperBound.planar_approx_extend
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T11:48:16.545205+00:00
-- url     : https://prove2.me/theorems/0ee193fe-3f30-4a35-be40-85365bcab3c4
-- title:
--   Proposition 2.1(i) — every point of $L^2$ extends to a solution of (8)
-- statement:
--   Let $\nu$ be a positive integer and $(x_1,x_2,x_3)\in L^2$, that is,
--   $$\sqrt{x_1^2+x_2^2}\le x_3.$$
--   Then there exist $\xi^j,\eta^j$, $j=0,\dots,\nu$, such that $(x_1,x_2,x_3,\xi,\eta)$ satisfies system (8).
--
--   Together with part (ii) this says that the system (8), $\Pi^{(\nu)}(x_1,x_2,x_3,u)\ge0$, is a polyhedral $\delta(\nu)$-approximation of $L^2$.
--
--   **Formalization Note** The hypothesis $\nu\ge1$ is the paper's "positive integer $\nu$"; it matters, since for $\nu=0$ the constraint (8c) involves $\tan(\pi/2)$, which Lean evaluates to $0$.
-- source:
--   Ben-Tal & Nemirovski, On Polyhedral Approximations of the Second-Order Cone, Math. Oper. Res. 26(2):193–205 (2001), p. 199, Proposition 2.1, part (i) of the proof statement

import Mathlib
import Definitions.Def_PolyhedralSOC_UpperBound_System8

namespace PolyhedralSOC.UpperBound

/-- Ben-Tal & Nemirovski, *On Polyhedral Approximations of the Second-Order Cone*,
Math. Oper. Res. 26(2):193–205 (2001), Proposition 2.1, part (i), p. 199 (PDF p. 7;
proof p. 200): for every positive integer `ν`, if `(x₁, x₂, x₃) ∈ L²`, i.e.
`√(x₁² + x₂²) ≤ x₃`, then `(x₁, x₂, x₃)` can be extended to a solution of (8). -/
theorem planar_approx_extend (ν : ℕ) (hν : 1 ≤ ν) (x₁ x₂ x₃ : ℝ)
    (hx : Real.sqrt (x₁ ^ 2 + x₂ ^ 2) ≤ x₃) :
    ∃ ξ η : ℕ → ℝ, System8 ν x₁ x₂ x₃ ξ η := by sorry

end PolyhedralSOC.UpperBound
