-- Prove2me | Theorems.Thm_VolunteerEngage_Bellman_betaLow_pos
-- name    : VolunteerEngage.Bellman.betaLow_pos
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:40:29.955974+00:00
-- url     : https://prove2.me/theorems/72db7c30-a35c-4337-b342-22cc60e81f76
-- title:
--   Online Supplement §F, p. 13 — β̲ = −inf ϕ(y) > 0
-- statement:
--   Fix parameters satisfying the standing assumptions, with engagement cost $c$ on $A=[\theta_0,\theta_L]$ and conjugate $\phi(y)=\sup_{x\in A}\{yx-c(x)\}$. Then the lower bound of the shooting parameter is strictly positive:
--
--   $$\underline\beta=-\inf_{y\le p}\phi(y)>0 .$$
--
--   The initial value problems IVP($\beta$) are studied for $\beta>\underline\beta$. Positivity of $\underline\beta$ is what yields $\beta^*>0$ in Theorem 1.
--
--   **Formalization Note.** The infimum is taken over $y\le p$ (the corrected reading of the printed $-\inf\phi(y)$; see the Setting). It agrees with the printed value when $\theta_L\ge0$.
-- source:
--   Ata, Tongarlak, Lee, Field, A Dynamic Model for Managing Volunteer Engagement, arXiv:2312.02920v2, Online Supplement p. 13, §F, before (F10)

import Mathlib
import Definitions.Def_VolunteerEngage_Bellman_Setting

namespace VolunteerEngage.Bellman

open Filter Topology

/-- Online Supplement p. 13, before (F10): `β̲ = -inf ϕ(y) > 0` (infimum over `y ≤ p`). -/
theorem betaLow_pos (M : Model) (hM : M.Standing) : 0 < betaLow M := by sorry

end VolunteerEngage.Bellman
