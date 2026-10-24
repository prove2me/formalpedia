-- Prove2me | Theorems.Thm_VolunteerEngage_Bellman_lemma_16
-- name    : VolunteerEngage.Bellman.lemma_16
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:41:12.915983+00:00
-- url     : https://prove2.me/theorems/79732ead-2e48-4ca6-9826-8ca1a2b29a84
-- title:
--   Lemma 16, Online Supplement p. 17 — β₂ > β₁ > β̲ and β₂ ∈ D imply β₁ ∈ D
-- statement:
--   Fix parameters satisfying the standing assumptions, with $\phi$, $\underline\beta$, IVP($\beta$) and the sets $\mathcal I$, $\mathcal D$ as in the mission's Setting. If $\beta_2>\beta_1>\underline\beta$ and $\beta_2\in\mathcal D$, then $\beta_1\in\mathcal D$.
--
--   So $\mathcal D$ is an initial segment of $(\underline\beta,\infty)$, and $\mathcal I$ is a final segment.
--
--   **Formalization Note.** The standing assumptions are a hypothesis.
-- source:
--   Ata, Tongarlak, Lee, Field, A Dynamic Model for Managing Volunteer Engagement, arXiv:2312.02920v2, Online Supplement p. 17, Lemma 16

import Mathlib
import Definitions.Def_VolunteerEngage_Bellman_Setting

namespace VolunteerEngage.Bellman

open Filter Topology

/-- Lemma 16 (Online Supplement p. 17): if `β₂ > β₁ > β̲` and `β₂ ∈ D`, then `β₁ ∈ D`. -/
theorem lemma_16 (M : Model) (hM : M.Standing) :
    ∀ β₁ β₂ : ℝ, betaLow M < β₁ → β₁ < β₂ → β₂ ∈ Dset M → β₁ ∈ Dset M := by sorry

end VolunteerEngage.Bellman
