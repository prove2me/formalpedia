-- Prove2me | Theorems.Thm_VolunteerEngage_Bellman_lemma_6
-- name    : VolunteerEngage.Bellman.lemma_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:40:24.624029+00:00
-- url     : https://prove2.me/theorems/e2d878bc-108c-4686-9158-c0ce9e6d9358
-- title:
--   Lemma 6, Online Supplement p. 14 — v_β(x) is increasing and continuous in β
-- statement:
--   Fix parameters $L,\theta_0,(\eta_l),(c_l),p,\kappa,\sigma$ satisfying the standing assumptions, with breakpoints $\theta_l$, engagement cost $c(\cdot)$ on $A=[\theta_0,\theta_L]$ and its conjugate $\phi(y)=\sup_{x\in A}\{yx-c(x)\}$. Let $\underline\beta=-\inf\{\phi(y):y\le p\}$ and, for $\beta\in\mathbb R$, call a function $v$ on $[0,\infty)$ a **solution of IVP($\beta$)** if $v$ is continuously differentiable on $[0,\infty)$ (one-sided derivative at $0$), $v(0)=0$, and
--
--   $$\beta=\tfrac12\sigma^2v'(x)+x\kappa\,(p-v(x))-\phi(p-v(x)),\qquad x\ge0.$$
--
--   Write $v_\beta$ for a solution of IVP($\beta$). Then:
--
--   1. **(increasing in $\beta$)** if $\underline\beta<\beta_1<\beta_2$, then $v_{\beta_1}(x)<v_{\beta_2}(x)$ for every $x>0$;
--   2. **(continuous in $\beta$)** for every $\beta>\underline\beta$ and every $x\ge0$, $v_{\beta'}(x)\to v_\beta(x)$ as $\beta'\to\beta$ with $\beta'>\underline\beta$; that is, for every $\varepsilon>0$ there is $\delta>0$ such that $|v_{\beta'}(x)-v_\beta(x)|<\varepsilon$ whenever $\beta'>\underline\beta$ and $|\beta'-\beta|<\delta$.
--
--   Monotone and continuous dependence on $\beta$ is the basis of the shooting argument.
--
--   **Formalization Note.** $v_\beta$ ("the" solution of IVP($\beta$), unique by Lemma 4) is never chosen: the statement quantifies over every pair $(v,v')$ with `IsIVPSol M β v v'`. The standing assumptions of the Setting (`M.Standing`) are a hypothesis. Strict monotonicity in $\beta$ is stated for $x>0$ only, since $v_\beta(0)=0$ for every $\beta$. Continuity is pointwise in $x$, as printed.
-- source:
--   Ata, Tongarlak, Lee, Field, A Dynamic Model for Managing Volunteer Engagement, arXiv:2312.02920v2, Online Supplement p. 14, Lemma 6

import Mathlib
import Definitions.Def_VolunteerEngage_Bellman_Setting

namespace VolunteerEngage.Bellman

open Filter Topology

/-- Lemma 6 (Online Supplement p. 14): for `β > β̲`, `v_β(x)` is increasing in `β` (for every
`x > 0`; all solutions vanish at `0`) and continuous in `β` (for every `x ≥ 0`). -/
theorem lemma_6 (M : Model) (hM : M.Standing) :
    (∀ β₁ β₂ : ℝ, betaLow M < β₁ → β₁ < β₂ →
      ∀ v₁ v₁' v₂ v₂' : ℝ → ℝ, IsIVPSol M β₁ v₁ v₁' → IsIVPSol M β₂ v₂ v₂' →
        ∀ x : ℝ, 0 < x → v₁ x < v₂ x) ∧
    (∀ β : ℝ, betaLow M < β → ∀ v v' : ℝ → ℝ, IsIVPSol M β v v' →
      ∀ x : ℝ, 0 ≤ x → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ β' : ℝ, betaLow M < β' → |β' - β| < δ →
          ∀ w w' : ℝ → ℝ, IsIVPSol M β' w w' → |w x - v x| < ε) := by sorry

end VolunteerEngage.Bellman
