-- Prove2me | Theorems.Thm_VolunteerEngage_Bellman_lemma_10
-- name    : VolunteerEngage.Bellman.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:40:29.501931+00:00
-- url     : https://prove2.me/theorems/5ed8318b-d367-4d30-beef-5faf583ebf5d
-- title:
--   Lemma 10, Online Supplement p. 16 — β ∈ D iff v′_β(x₀) < 0 for some x₀ > 0
-- statement:
--   Fix parameters $L,\theta_0,(\eta_l),(c_l),p,\kappa,\sigma$ satisfying the standing assumptions, with breakpoints $\theta_l$, engagement cost $c(\cdot)$ on $A=[\theta_0,\theta_L]$ and its conjugate $\phi(y)=\sup_{x\in A}\{yx-c(x)\}$. Let $\underline\beta=-\inf\{\phi(y):y\le p\}$ and, for $\beta\in\mathbb R$, call a function $v$ on $[0,\infty)$ a **solution of IVP($\beta$)** if $v$ is continuously differentiable on $[0,\infty)$ (one-sided derivative at $0$), $v(0)=0$, and
--
--   $$\beta=\tfrac12\sigma^2v'(x)+x\kappa\,(p-v(x))-\phi(p-v(x)),\qquad x\ge0.$$
--
--   Let $\mathcal D$ be the set of $\beta>\underline\beta$ for which IVP($\beta$) has a solution that is nondecreasing on $(0,x_\beta)$ and nonincreasing on $(x_\beta,\infty)$ for some $x_\beta$. Then for every $\beta>\underline\beta$ and every solution $v$ of IVP($\beta$),
--
--   $$\beta\in\mathcal D\iff \exists\,x_0>0:\ v'(x_0)<0 .$$
--
--   Combined with Corollary 2, this splits $(\underline\beta,\infty)$ into $\mathcal I$ and $\mathcal D$.
--
--   **Formalization Note.** $v_\beta$ ("the" solution of IVP($\beta$), unique by Lemma 4) is never chosen: the statement quantifies over every pair $(v,v')$ with `IsIVPSol M β v v'`. The standing assumptions of the Setting (`M.Standing`) are a hypothesis.
-- source:
--   Ata, Tongarlak, Lee, Field, A Dynamic Model for Managing Volunteer Engagement, arXiv:2312.02920v2, Online Supplement p. 16, Lemma 10

import Mathlib
import Definitions.Def_VolunteerEngage_Bellman_Setting

namespace VolunteerEngage.Bellman

open Filter Topology

/-- Lemma 10 (Online Supplement p. 16): for `β > β̲`, `β ∈ D` iff `v_β'(x₀) < 0` for some
`x₀ > 0`. -/
theorem lemma_10 (M : Model) (hM : M.Standing) :
    ∀ β : ℝ, betaLow M < β → ∀ v v' : ℝ → ℝ, IsIVPSol M β v v' →
      (β ∈ Dset M ↔ ∃ x₀ : ℝ, 0 < x₀ ∧ v' x₀ < 0) := by sorry

end VolunteerEngage.Bellman
