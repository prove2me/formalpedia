-- Prove2me | Theorems.Thm_VolunteerEngage_Bellman_corollary_4
-- name    : VolunteerEngage.Bellman.corollary_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:41:17.176104+00:00
-- url     : https://prove2.me/theorems/3c47b72e-f0ad-4737-b7f0-722cf55728be
-- title:
--   Corollary 4, Online Supplement p. 19 — (β∗, v_β∗) solve the Bellman equation (68)–(69)
-- statement:
--   Fix parameters satisfying the standing assumptions, with $\phi$, $\underline\beta$, IVP($\beta$) and the sets $\mathcal I$, $\mathcal D$ as in the mission's Setting. Let $\beta^*=\inf\mathcal I$. Then:
--
--   1. IVP($\beta^*$) has a solution;
--   2. every solution $v$ of IVP($\beta^*$) solves the Bellman equation (68)–(69) with constant $\beta^*$. That is, $v$ is continuously differentiable on $[0,\infty)$, satisfies (68) for $x\ge0$, $v(0)=0$, is strictly increasing on $[0,\infty)$, and $v(x)\to p$ as $x\to\infty$.
--
--   **Formalization Note.** $v_\beta$ ("the" solution of IVP($\beta$), unique by Lemma 4) is never chosen: the statement quantifies over every pair $(v,v')$ with `IsIVPSol M β v v'`. The standing assumptions of the Setting (`M.Standing`) are a hypothesis. The existence clause makes explicit what the paper's notation $v_{\beta^*}$ presupposes.
-- source:
--   Ata, Tongarlak, Lee, Field, A Dynamic Model for Managing Volunteer Engagement, arXiv:2312.02920v2, Online Supplement p. 19, Corollary 4

import Mathlib
import Definitions.Def_VolunteerEngage_Bellman_Setting

namespace VolunteerEngage.Bellman

open Filter Topology

/-- Corollary 4 (Online Supplement p. 19): `(β*, v_{β*})` solves the Bellman equation (68)–(69):
IVP(β*) has a solution, and every solution of IVP(β*) solves (68)–(69). -/
theorem corollary_4 (M : Model) (hM : M.Standing) :
    (∃ v v' : ℝ → ℝ, IsIVPSol M (betaStar M) v v') ∧
      ∀ v v' : ℝ → ℝ, IsIVPSol M (betaStar M) v v' → IsBellmanSol M (betaStar M) v v' := by sorry

end VolunteerEngage.Bellman
