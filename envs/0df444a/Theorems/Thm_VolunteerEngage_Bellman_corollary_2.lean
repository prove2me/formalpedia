-- Prove2me | Theorems.Thm_VolunteerEngage_Bellman_corollary_2
-- name    : VolunteerEngage.Bellman.corollary_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:40:37.444418+00:00
-- url     : https://prove2.me/theorems/3f176217-86e7-42da-8817-753061af86da
-- title:
--   Corollary 2, Online Supplement p. 16 — nondecreasing on (a, b) ⊂ (0, ∞) implies increasing, nonincreasing implies decreasing
-- statement:
--   Fix parameters $L,\theta_0,(\eta_l),(c_l),p,\kappa,\sigma$ satisfying the standing assumptions, with breakpoints $\theta_l$, engagement cost $c(\cdot)$ on $A=[\theta_0,\theta_L]$ and its conjugate $\phi(y)=\sup_{x\in A}\{yx-c(x)\}$. Let $\underline\beta=-\inf\{\phi(y):y\le p\}$ and, for $\beta\in\mathbb R$, call a function $v$ on $[0,\infty)$ a **solution of IVP($\beta$)** if $v$ is continuously differentiable on $[0,\infty)$ (one-sided derivative at $0$), $v(0)=0$, and
--
--   $$\beta=\tfrac12\sigma^2v'(x)+x\kappa\,(p-v(x))-\phi(p-v(x)),\qquad x\ge0.$$
--
--   Let $\beta>\underline\beta$, let $v$ solve IVP($\beta$), and let $(a,b)\subset(0,\infty)$. Then:
--
--   1. if $v$ is nondecreasing on $(a,b)$, it is strictly increasing on $(a,b)$;
--   2. if $v$ is nonincreasing on $(a,b)$, it is strictly decreasing on $(a,b)$.
--
--   It rules out flat pieces of $v_\beta$. This is why the sets $\mathcal I$ and $\mathcal D$ can be described with weak or strict monotonicity interchangeably.
--
--   **Formalization Note.** $v_\beta$ ("the" solution of IVP($\beta$), unique by Lemma 4) is never chosen: the statement quantifies over every pair $(v,v')$ with `IsIVPSol M β v v'`. The standing assumptions of the Setting (`M.Standing`) are a hypothesis. The condition $(a,b)\subset(0,\infty)$ is encoded as $a\ge0$; $b$ is arbitrary (the claim is empty when $b\le a$).
-- source:
--   Ata, Tongarlak, Lee, Field, A Dynamic Model for Managing Volunteer Engagement, arXiv:2312.02920v2, Online Supplement p. 16, Corollary 2

import Mathlib
import Definitions.Def_VolunteerEngage_Bellman_Setting

namespace VolunteerEngage.Bellman

open Filter Topology

/-- Corollary 2 (Online Supplement p. 16): for `β > β̲` and `(a, b) ⊂ (0, ∞)`, if `v_β` is
nondecreasing on `(a, b)` it is increasing there, and if it is nonincreasing on `(a, b)` it is
decreasing there. -/
theorem corollary_2 (M : Model) (hM : M.Standing) :
    ∀ β : ℝ, betaLow M < β → ∀ v v' : ℝ → ℝ, IsIVPSol M β v v' →
      ∀ a b : ℝ, 0 ≤ a →
        (MonotoneOn v (Set.Ioo a b) → StrictMonoOn v (Set.Ioo a b)) ∧
        (AntitoneOn v (Set.Ioo a b) → StrictAntiOn v (Set.Ioo a b)) := by sorry

end VolunteerEngage.Bellman
