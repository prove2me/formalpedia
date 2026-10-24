-- Prove2me | Theorems.Thm_VolunteerEngage_Bellman_lemma_14
-- name    : VolunteerEngage.Bellman.lemma_14
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:41:09.244973+00:00
-- url     : https://prove2.me/theorems/7b69efc0-82f0-40a3-9d0f-fc97bd85f2f3
-- title:
--   Lemma 14, Online Supplement p. 17 — (β ∈ I and v_β unbounded) iff v_β(x₀) ≥ p for some x₀ > 0
-- statement:
--   Fix parameters satisfying the standing assumptions, with $\phi$, $\underline\beta$, IVP($\beta$) and the sets $\mathcal I$, $\mathcal D$ as in the mission's Setting. For every $\beta>\underline\beta$ and every solution $v$ of IVP($\beta$),
--
--   $$\big(\beta\in\mathcal I\ \text{and } v \text{ is unbounded on } [0,\infty)\big)\iff \exists\,x_0>0:\ v(x_0)\ge p .$$
--
--   It identifies the members of $\mathcal I$ that overshoot the target level $p$.
--
--   **Formalization Note.** $v_\beta$ ("the" solution of IVP($\beta$), unique by Lemma 4) is never chosen: the statement quantifies over every pair $(v,v')$ with `IsIVPSol M β v v'`. The standing assumptions of the Setting (`M.Standing`) are a hypothesis. "Unbounded" is read as unbounded above on $[0,\infty)$, which for an increasing function starting at $v(0)=0$ is the same as unbounded.
-- source:
--   Ata, Tongarlak, Lee, Field, A Dynamic Model for Managing Volunteer Engagement, arXiv:2312.02920v2, Online Supplement p. 17, Lemma 14

import Mathlib
import Definitions.Def_VolunteerEngage_Bellman_Setting

namespace VolunteerEngage.Bellman

open Filter Topology

/-- Lemma 14 (Online Supplement p. 17): for `β > β̲`, `β ∈ I` and `v_β` is unbounded iff
`v_β(x₀) ≥ p` for some `x₀ > 0`. -/
theorem lemma_14 (M : Model) (hM : M.Standing) :
    ∀ β : ℝ, betaLow M < β → ∀ v v' : ℝ → ℝ, IsIVPSol M β v v' →
      ((β ∈ Iset M ∧ ¬ BddAbove (v '' Set.Ici 0)) ↔ ∃ x₀ : ℝ, 0 < x₀ ∧ M.p ≤ v x₀) := by sorry

end VolunteerEngage.Bellman
