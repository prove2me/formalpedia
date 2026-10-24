-- Prove2me | Theorems.Thm_VolunteerEngage_Bellman_theorem_1
-- name    : VolunteerEngage.Bellman.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:41:20.796046+00:00
-- url     : https://prove2.me/theorems/c38ec9b1-5e81-4de2-a5ee-b9c51e53b21a
-- title:
--   Theorem 1, p. 21 — the Bellman equation (68)–(69) has a solution (β∗, v) with β∗ > 0 and v increasing and C¹
-- statement:
--   Fix parameters $L,\theta_0,(\eta_l),(c_l),p,\kappa,\sigma$ of the drift-rate control problem satisfying the standing assumptions, with engagement cost $c$ on $A=[\theta_0,\theta_L]$ given by (52) and its convex conjugate $\phi(y)=\sup_{x\in A}\{yx-c(x)\}$.
--
--   Then there exist a constant $\beta>0$ and a function $v$, continuously differentiable on $[0,\infty)$, such that
--
--   $$\beta=\tfrac12\sigma^2v'(x)+x\kappa\,(p-v(x))-\phi(p-v(x)),\qquad x\ge0,$$
--
--   $v(0)=0$, $v$ is strictly increasing on $[0,\infty)$, and $\lim_{x\to\infty}v(x)=p$.
--
--   In the paper, the constant $\beta$ is shown (Theorem 2) to be the optimal long-run average cost of the drift-rate control problem, and the solution $v$ defines the thresholds $\tau_l=v^{-1}(p-c_l)$ of the paper's nested threshold policy.
--
--   **Formalization Note.** "Continuously differentiable" is a pair $(v,v')$ with $v'$ continuous on $[0,\infty)$ and $v'(x)$ the derivative of $v$ within $[0,\infty)$ at every $x\ge0$ (one-sided at $0$). "Increasing" is strict. The paper's standing assumptions are an explicit hypothesis; they follow from the queueing model's primitives. $\beta$ and $v$ are existentially quantified, as in the paper.
-- source:
--   Ata, Tongarlak, Lee, Field, A Dynamic Model for Managing Volunteer Engagement, arXiv:2312.02920v2, p. 21, Theorem 1

import Mathlib
import Definitions.Def_VolunteerEngage_Bellman_Setting

namespace VolunteerEngage.Bellman

open Filter Topology

/-- Theorem 1 (p. 21): the Bellman equation (68)–(69) has a solution `(β*, v)` with `β* > 0` and `v`
increasing and continuously differentiable. -/
theorem theorem_1 (M : Model) (hM : M.Standing) :
    ∃ β : ℝ, 0 < β ∧ ∃ v v' : ℝ → ℝ, IsBellmanSol M β v v' := by sorry

end VolunteerEngage.Bellman
