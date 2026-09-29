-- Prove2me | Theorems.Thm_PolyhedralSOC_UpperBound_planar_approx_quality
-- name    : PolyhedralSOC.UpperBound.planar_approx_quality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:48:40.535505+00:00
-- url     : https://prove2.me/theorems/11b2ade7-6f13-444e-bc98-51f70442ef1f
-- title:
--   Proposition 2.1(ii) — solutions of (8) satisfy $\|(x_1,x_2)\|_2\le(1+\delta(\nu))x_3$
-- statement:
--   Let $\nu$ be a positive integer and suppose $(x_1,x_2,x_3)$ can be extended, by some $\xi^j,\eta^j$ ($j=0,\dots,\nu$), to a solution of system (8). Then
--   $$\|(x_1,x_2)\|_2=\sqrt{x_1^2+x_2^2}\le(1+\delta(\nu))\,x_3,\qquad \delta(\nu)=\frac{1}{\cos\big(\frac{\pi}{2^{\nu+1}}\big)}-1.$$
--
--   Together with part (i) this says that system (8) is a polyhedral $\delta(\nu)$-approximation of $L^2$.
--
--   **Formalization Note** The conclusion holds for every solution of (8), not only for the one constructed in part (i).
-- source:
--   Ben-Tal & Nemirovski, On Polyhedral Approximations of the Second-Order Cone, Math. Oper. Res. 26(2):193–205 (2001), p. 199, Proposition 2.1, part (ii) of the proof statement, Eq. (9)

import Mathlib
import Definitions.Def_PolyhedralSOC_UpperBound_System8

namespace PolyhedralSOC.UpperBound

/-- Ben-Tal & Nemirovski, *On Polyhedral Approximations of the Second-Order Cone*,
Math. Oper. Res. 26(2):193–205 (2001), Proposition 2.1, part (ii), p. 199 (PDF p. 7;
proof p. 200): for every positive integer `ν`, if `(x₁, x₂, x₃)` can be extended to a
solution of (8), then `‖(x₁, x₂)‖₂ ≤ (1 + δ(ν)) x₃` with `δ(ν) = 1/cos(π/2^{ν+1}) − 1`. -/
theorem planar_approx_quality (ν : ℕ) (hν : 1 ≤ ν) (x₁ x₂ x₃ : ℝ) (ξ η : ℕ → ℝ)
    (h : System8 ν x₁ x₂ x₃ ξ η) :
    Real.sqrt (x₁ ^ 2 + x₂ ^ 2) ≤ (1 + delta ν) * x₃ := by sorry

end PolyhedralSOC.UpperBound
