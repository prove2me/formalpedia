-- Prove2me | Theorems.Thm_VolunteerEngage_Bellman_lemma_12
-- name    : VolunteerEngage.Bellman.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:40:33.801874+00:00
-- url     : https://prove2.me/theorems/9ab39add-0f22-4ef7-a601-1b25dabcbb47
-- title:
--   Lemma 12, Online Supplement p. 17 — β ∈ D implies v_β(x) → −∞
-- statement:
--   Fix parameters satisfying the standing assumptions, with $\phi$, $\underline\beta$, IVP($\beta$) and the sets $\mathcal I$, $\mathcal D$ as in the mission's Setting. If $\beta>\underline\beta$ and $\beta\in\mathcal D$, then every solution $v$ of IVP($\beta$) satisfies
--
--   $$\lim_{x\to\infty}v(x)=-\infty .$$
--
--   On $\mathcal D$ the solution therefore cannot satisfy the boundary condition $v(x)\to p$ of the Bellman equation.
--
--   **Formalization Note.** $v_\beta$ ("the" solution of IVP($\beta$), unique by Lemma 4) is never chosen: the statement quantifies over every pair $(v,v')$ with `IsIVPSol M β v v'`. The standing assumptions of the Setting (`M.Standing`) are a hypothesis.
-- source:
--   Ata, Tongarlak, Lee, Field, A Dynamic Model for Managing Volunteer Engagement, arXiv:2312.02920v2, Online Supplement p. 17, Lemma 12

import Mathlib
import Definitions.Def_VolunteerEngage_Bellman_Setting

namespace VolunteerEngage.Bellman

open Filter Topology

/-- Lemma 12 (Online Supplement p. 17): if `β > β̲` and `β ∈ D`, then `v_β(x) → -∞`. -/
theorem lemma_12 (M : Model) (hM : M.Standing) :
    ∀ β : ℝ, betaLow M < β → β ∈ Dset M → ∀ v v' : ℝ → ℝ, IsIVPSol M β v v' →
      Tendsto v atTop atBot := by sorry

end VolunteerEngage.Bellman
