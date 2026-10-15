-- Prove2me | Theorems.Thm_VolunteerEngage_Bellman_lemma_18
-- name    : VolunteerEngage.Bellman.lemma_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:41:12.477994+00:00
-- url     : https://prove2.me/theorems/9897ebe6-837f-4a43-b47f-feb02e05b92d
-- title:
--   Lemma 18, Online Supplement p. 17 — β∗ ∈ I and v_β∗ is bounded
-- statement:
--   Fix parameters satisfying the standing assumptions, with $\phi$, $\underline\beta$, IVP($\beta$) and the sets $\mathcal I$, $\mathcal D$ as in the mission's Setting. Let $\beta^*=\inf\mathcal I$. Then:
--
--   1. $\beta^*\in\mathcal I$;
--   2. every solution $v$ of IVP($\beta^*$) is bounded on $[0,\infty)$: there is $C$ with $|v(x)|\le C$ for all $x\ge0$.
--
--   **Formalization Note.** $v_\beta$ ("the" solution of IVP($\beta$), unique by Lemma 4) is never chosen: the statement quantifies over every pair $(v,v')$ with `IsIVPSol M β v v'`. The standing assumptions of the Setting (`M.Standing`) are a hypothesis. Nothing about $\mathcal I$ is assumed.
-- source:
--   Ata, Tongarlak, Lee, Field, A Dynamic Model for Managing Volunteer Engagement, arXiv:2312.02920v2, Online Supplement p. 17, Lemma 18

import Mathlib
import Definitions.Def_VolunteerEngage_Bellman_Setting

namespace VolunteerEngage.Bellman

open Filter Topology

/-- Lemma 18 (Online Supplement p. 17): `β* ∈ I` and `v_{β*}` is bounded. -/
theorem lemma_18 (M : Model) (hM : M.Standing) :
    betaStar M ∈ Iset M ∧
      ∀ v v' : ℝ → ℝ, IsIVPSol M (betaStar M) v v' →
        ∃ C : ℝ, ∀ x : ℝ, 0 ≤ x → |v x| ≤ C := by sorry

end VolunteerEngage.Bellman
