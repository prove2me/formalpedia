-- Prove2me | Theorems.Thm_VolunteerEngage_Bellman_lemma_20
-- name    : VolunteerEngage.Bellman.lemma_20
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:41:17.966101+00:00
-- url     : https://prove2.me/theorems/73431224-534c-40f4-a832-aa6f7fa5aad3
-- title:
--   Lemma 20, Online Supplement p. 18 — v_β∗(x) → p as x → ∞
-- statement:
--   Fix parameters satisfying the standing assumptions, with $\phi$, $\underline\beta$, IVP($\beta$) and the sets $\mathcal I$, $\mathcal D$ as in the mission's Setting. Let $\beta^*=\inf\mathcal I$. Every solution $v$ of IVP($\beta^*$) satisfies
--
--   $$\lim_{x\to\infty}v(x)=p .$$
--
--   This is the boundary condition at infinity of the Bellman equation (69).
--
--   **Formalization Note.** $v_\beta$ ("the" solution of IVP($\beta$), unique by Lemma 4) is never chosen: the statement quantifies over every pair $(v,v')$ with `IsIVPSol M β v v'`. The standing assumptions of the Setting (`M.Standing`) are a hypothesis.
-- source:
--   Ata, Tongarlak, Lee, Field, A Dynamic Model for Managing Volunteer Engagement, arXiv:2312.02920v2, Online Supplement p. 18, Lemma 20

import Mathlib
import Definitions.Def_VolunteerEngage_Bellman_Setting

namespace VolunteerEngage.Bellman

open Filter Topology

/-- Lemma 20 (Online Supplement p. 18): `v_{β*}(x) → p` as `x → ∞`. -/
theorem lemma_20 (M : Model) (hM : M.Standing) :
    ∀ v v' : ℝ → ℝ, IsIVPSol M (betaStar M) v v' → Tendsto v atTop (𝓝 M.p) := by sorry

end VolunteerEngage.Bellman
