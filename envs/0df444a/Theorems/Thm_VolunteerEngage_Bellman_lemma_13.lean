-- Prove2me | Theorems.Thm_VolunteerEngage_Bellman_lemma_13
-- name    : VolunteerEngage.Bellman.lemma_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:41:07.060061+00:00
-- url     : https://prove2.me/theorems/350b4fea-3a04-4131-a2d9-7367a881b0a9
-- title:
--   Lemma 13, Online Supplement p. 17 — I ≠ ∅ and D ≠ ∅
-- statement:
--   Fix parameters satisfying the standing assumptions, with $\phi$, $\underline\beta$, IVP($\beta$) and the sets $\mathcal I$, $\mathcal D$ as in the mission's Setting. Here $\mathcal I$ is the set of $\beta>\underline\beta$ for which IVP($\beta$) has a strictly increasing solution, and $\mathcal D$ is the set of $\beta>\underline\beta$ for which it has a solution that rises and then falls. Then
--
--   $$\mathcal I\neq\emptyset\quad\text{and}\quad\mathcal D\neq\emptyset .$$
--
--   Both sets being nonempty is what makes $\beta^*=\inf\mathcal I$ a meaningful shooting parameter.
--
--   **Formalization Note.** The standing assumptions are a hypothesis.
-- source:
--   Ata, Tongarlak, Lee, Field, A Dynamic Model for Managing Volunteer Engagement, arXiv:2312.02920v2, Online Supplement p. 17, Lemma 13

import Mathlib
import Definitions.Def_VolunteerEngage_Bellman_Setting

namespace VolunteerEngage.Bellman

open Filter Topology

/-- Lemma 13 (Online Supplement p. 17): `I ≠ ∅` and `D ≠ ∅`. -/
theorem lemma_13 (M : Model) (hM : M.Standing) :
    (Iset M).Nonempty ∧ (Dset M).Nonempty := by sorry

end VolunteerEngage.Bellman
