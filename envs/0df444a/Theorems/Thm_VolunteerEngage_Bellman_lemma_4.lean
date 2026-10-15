-- Prove2me | Theorems.Thm_VolunteerEngage_Bellman_lemma_4
-- name    : VolunteerEngage.Bellman.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:40:36.086949+00:00
-- url     : https://prove2.me/theorems/62ad30e2-6ecc-4ed7-9b64-172f5b5ec9c1
-- title:
--   Lemma 4, Online Supplement p. 14 — IVP(β) has a unique C¹ solution on [0, ∞) for β > β̲
-- statement:
--   Fix parameters $L,\theta_0,(\eta_l),(c_l),p,\kappa,\sigma$ satisfying the standing assumptions, with breakpoints $\theta_l$, engagement cost $c(\cdot)$ on $A=[\theta_0,\theta_L]$ and its conjugate $\phi(y)=\sup_{x\in A}\{yx-c(x)\}$. Let $\underline\beta=-\inf\{\phi(y):y\le p\}$ and, for $\beta\in\mathbb R$, call a function $v$ on $[0,\infty)$ a **solution of IVP($\beta$)** if $v$ is continuously differentiable on $[0,\infty)$ (one-sided derivative at $0$), $v(0)=0$, and
--
--   $$\beta=\tfrac12\sigma^2v'(x)+x\kappa\,(p-v(x))-\phi(p-v(x)),\qquad x\ge0.$$
--
--   Then for every $\beta>\underline\beta$:
--
--   1. IVP($\beta$) has a solution;
--   2. any two solutions $v,w$ of IVP($\beta$) agree on $[0,\infty)$.
--
--   This solution is denoted $v_\beta$; the shooting argument studies how it varies with $\beta$.
--
--   **Formalization Note.** Solutions are pairs $(v,v')$ of functions on $\mathbb R$; only their values on $[0,\infty)$ are constrained, so uniqueness is stated as agreement on $[0,\infty)$.
-- source:
--   Ata, Tongarlak, Lee, Field, A Dynamic Model for Managing Volunteer Engagement, arXiv:2312.02920v2, Online Supplement p. 14, Lemma 4

import Mathlib
import Definitions.Def_VolunteerEngage_Bellman_Setting

namespace VolunteerEngage.Bellman

open Filter Topology

/-- Lemma 4 (Online Supplement p. 14): for `β > β̲`, IVP(β) has a continuously differentiable
solution on `[0, ∞)`, and any two solutions agree on `[0, ∞)`. -/
theorem lemma_4 (M : Model) (hM : M.Standing) :
    ∀ β : ℝ, betaLow M < β →
      (∃ v v' : ℝ → ℝ, IsIVPSol M β v v') ∧
      ∀ v v' w w' : ℝ → ℝ, IsIVPSol M β v v' → IsIVPSol M β w w' →
        ∀ x : ℝ, 0 ≤ x → w x = v x := by sorry

end VolunteerEngage.Bellman
