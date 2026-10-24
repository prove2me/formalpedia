-- Prove2me | Theorems.Thm_VolunteerEngage_Bellman_lemma_15
-- name    : VolunteerEngage.Bellman.lemma_15
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:41:10.889254+00:00
-- url     : https://prove2.me/theorems/314f4c34-af46-451a-9613-80a78e2a95f6
-- title:
--   Lemma 15, Online Supplement p. 17 — four equivalent descriptions of D
-- statement:
--   Fix parameters satisfying the standing assumptions, with $\phi$, $\underline\beta$, IVP($\beta$) and the sets $\mathcal I$, $\mathcal D$ as in the mission's Setting. Let $\beta>\underline\beta$ and let $v$ solve IVP($\beta$). The following are equivalent:
--
--   1. $\beta\in\mathcal D$;
--   2. there exists $x>0$ such that $v'(x)<0$;
--   3. there exists $x>0$ such that $v(x)<0$;
--   4. $\lim_{x\to\infty}v(x)=-\infty$.
--
--   The equivalence (1)⇔(3) is the form used to compare different values of $\beta$.
--
--   **Formalization Note.** $v_\beta$ ("the" solution of IVP($\beta$), unique by Lemma 4) is never chosen: the statement quantifies over every pair $(v,v')$ with `IsIVPSol M β v v'`. The standing assumptions of the Setting (`M.Standing`) are a hypothesis.
-- source:
--   Ata, Tongarlak, Lee, Field, A Dynamic Model for Managing Volunteer Engagement, arXiv:2312.02920v2, Online Supplement p. 17, Lemma 15

import Mathlib
import Definitions.Def_VolunteerEngage_Bellman_Setting

namespace VolunteerEngage.Bellman

open Filter Topology

/-- Lemma 15 (Online Supplement p. 17): for `β > β̲` the following are equivalent:
`β ∈ D`; `v_β'(x) < 0` for some `x > 0`; `v_β(x) < 0` for some `x > 0`; `v_β(x) → -∞`. -/
theorem lemma_15 (M : Model) (hM : M.Standing) :
    ∀ β : ℝ, betaLow M < β → ∀ v v' : ℝ → ℝ, IsIVPSol M β v v' →
      List.TFAE [β ∈ Dset M, ∃ x : ℝ, 0 < x ∧ v' x < 0, ∃ x : ℝ, 0 < x ∧ v x < 0,
        Tendsto v atTop atBot] := by sorry

end VolunteerEngage.Bellman
