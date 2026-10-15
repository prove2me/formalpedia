-- Prove2me | Theorems.Thm_VolunteerEngage_Bellman_lemma_17
-- name    : VolunteerEngage.Bellman.lemma_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:41:10.882984+00:00
-- url     : https://prove2.me/theorems/9c0020a5-602c-41a0-84a4-cb5ca902a5c6
-- title:
--   Lemma 17, Online Supplement p. 17 — β∗ = inf I > β̲
-- statement:
--   Fix parameters satisfying the standing assumptions, with $\phi$, $\underline\beta$, IVP($\beta$) and the sets $\mathcal I$, $\mathcal D$ as in the mission's Setting. Let $\beta^*=\inf\mathcal I$. Then
--
--   $$\beta^*>\underline\beta .$$
--
--   In particular, IVP($\beta^*$) lies in the range where the shooting lemmas apply.
--
--   **Formalization Note.** $\beta^*$ is the real infimum of $\mathcal I$; nothing about $\mathcal I$ (nonemptiness, a lower bound) is assumed.
-- source:
--   Ata, Tongarlak, Lee, Field, A Dynamic Model for Managing Volunteer Engagement, arXiv:2312.02920v2, Online Supplement p. 17, Lemma 17 (with the definition β∗ = inf I before it)

import Mathlib
import Definitions.Def_VolunteerEngage_Bellman_Setting

namespace VolunteerEngage.Bellman

open Filter Topology

/-- Lemma 17 (Online Supplement p. 17): `β* = inf I > β̲`. -/
theorem lemma_17 (M : Model) (hM : M.Standing) : betaLow M < betaStar M := by sorry

end VolunteerEngage.Bellman
