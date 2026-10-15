-- Prove2me | Theorems.Thm_OutpatientWalkIn_Triage_proposition_1_obs
-- name    : OutpatientWalkIn.Triage.proposition_1_obs
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:06:13.254526+00:00
-- url     : https://prove2.me/theorems/ea8d0f46-f4af-4c50-9228-effbffb49809
-- title:
--   Proposition 1, p. 16 (observable setting, Online App. D.3, p. 10) — an observable equilibrium exists at every allocation µ_S ∈ [0, µ)
-- statement:
--   Under the standing assumptions, for every allocation of appointment hours $\mu_S\in[0,\mu)$ (so that the walk-in hours $\mu_W=\mu-\mu_S$ are positive) there is a strategy $(\delta,p_W,p_B)$ that is an observable equilibrium at $\mu_S$:
--   $$\forall\,\mu_S\in[0,\mu)\ \ \exists\,(\delta,p_W,p_B):\ (\delta,p_W,p_B)\ \text{satisfies (6)–(10) at }\mu_S.$$
--
--   Proposition 1 describes this equilibrium in three regimes: schedule-and-balk (SnB) when $u^2_W(0)\le0$, schedule-walk-in-and-balk (SWB), and schedule-and-walk-in (SnW). Existence is what makes the strategic model's cost (Ob.P) defined at every allocation, so that the second part of Proposition 6 is not vacuous.
--
--   **Formalization Note** The observable setting is Proposition 1 with $C_G=0$, $\lambda_S=\lambda$ and $\lambda_W=0$ (Lemma 4, Appendix D.3). Only existence is stated, not the three-case description, which needs $w^{-1}$ and an implicit root $\delta^S_W$. At $\mu_S=0$, $\pi=1$ and every strategic patient walks in or balks; the statement covers this case.
-- source:
--   Liu, van Jaarsveld, Wang, Xiao, Managing Outpatient Service with Strategic Walk-ins, SSRN 3558209 (version of 2022-07-05), p. 16, Proposition 1 (observable setting: Online Appendix p. 10, D.3)

import Mathlib
import Definitions.Def_OutpatientWalkIn_Triage_Queue
import Definitions.Def_OutpatientWalkIn_Triage_Setting

namespace OutpatientWalkIn.Triage

theorem proposition_1_obs (M : Model) (hM : M.Standing) :
    ∀ μS ∈ Set.Ico 0 M.mu, ∃ e : ObsStrategy, M.IsObsEq μS e := by sorry

end OutpatientWalkIn.Triage
