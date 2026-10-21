-- Prove2me | Theorems.Thm_VolunteerEngage_Thresholds_eq_E9
-- name    : VolunteerEngage.Thresholds.eq_E9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:40:39.3853+00:00
-- url     : https://prove2.me/theorems/ebb57971-585e-4656-a572-c53abb0e0ea2
-- title:
--   (E9), Online Supplement p. 13 — the convex conjugate ϕ is piecewise linear with slope θ_{m−1} on (ĉ_{m−1}, ĉ_m]
-- statement:
--   Let the parameters satisfy the standing assumptions, let $\theta_0<\theta_1<\dots<\theta_L$ be the breakpoints (51), $c$ the piecewise linear engagement cost (52) on $A=[\theta_0,\theta_L]$ with slopes $c_1<\dots<c_L$, and $\phi(y)=\sup_{x\in A}\{yx-c(x)\}$ its convex conjugate (66). Then
--   $$\phi(y)=\begin{cases}\theta_0\,y, & y\le c_1,\\ \theta_{m-1}\,y-c(\theta_{m-1}), & c_{m-1}<y\le c_m,\ m=2,\dots,L,\\ \theta_L\,y-c(\theta_L), & y>c_L.\end{cases}$$
--
--   The conjugate of a convex piecewise linear cost is again piecewise linear, with the breakpoints of the cost as slopes and the slopes of the cost as breakpoints. On each threshold interval of the Bellman solution, this turns the Bellman equation (68) into a linear first-order equation, which is what makes the closed form of Proposition 3 possible.
--
--   **Formalization Note** The paper's Online Supplement writes $M$, $\hat c_m$ for the $L$, $c_m$ of the main text; they are the same objects. $\phi$ is defined by the supremum (66), not by this formula.
-- source:
--   Ata, Tongarlak, Lee, Field, A Dynamic Model for Managing Volunteer Engagement, arXiv:2312.02920v2, Online Supplement p. 13, (E9) (preamble of §E on Online Supplement p. 12)

import Mathlib
import Definitions.Def_VolunteerEngage_Thresholds_Setting

namespace VolunteerEngage.Thresholds

/-- (E9), Online Supplement p. 13: under the standing assumptions the convex conjugate
`ϕ(y) = sup_{x ∈ [θ0, θ_L]} {y x - c(x)}` is piecewise linear:
`ϕ(y) = θ0 y` for `y ≤ ĉ_1`; `ϕ(y) = θ_{m-1} y - c(θ_{m-1})` for `ĉ_{m-1} < y ≤ ĉ_m`,
`m = 2, …, L`; and `ϕ(y) = θ_L y - c(θ_L)` for `y > ĉ_L` (here `ĉ_m = c_m`, `M = L`). -/
theorem eq_E9 (M : Model) (hM : M.Standing) :
    (∀ y : ℝ, y ≤ M.c 1 → phi M y = M.θ 0 * y) ∧
    (∀ m ∈ Finset.Icc 2 M.L, ∀ y : ℝ, M.c (m - 1) < y → y ≤ M.c m →
      phi M y = M.θ (m - 1) * y - cost M (M.θ (m - 1))) ∧
    (∀ y : ℝ, M.c M.L < y → phi M y = M.θ M.L * y - cost M (M.θ M.L)) := by sorry

end VolunteerEngage.Thresholds
