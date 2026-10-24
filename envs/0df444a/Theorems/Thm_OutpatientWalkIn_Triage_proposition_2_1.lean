-- Prove2me | Theorems.Thm_OutpatientWalkIn_Triage_proposition_2_1
-- name    : OutpatientWalkIn.Triage.proposition_2_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:06:06.025467+00:00
-- url     : https://prove2.me/theorems/b1ed61eb-8069-4093-94b3-693a7efd3e70
-- title:
--   Proposition 2 (1), p. 22 — if µ_W ≤ µ̲_W, the observable equilibrium is in Regime SnB
-- statement:
--   Assume the standing assumptions and let $\underline\mu_W>0$ satisfy
--   $$R-C_W\,w(\lambda_E/\underline\mu_W)=0. \tag{15}$$
--   Let $\mu_S\in[0,\mu)$ with walk-in hours $\mu_W=\mu-\mu_S\le\underline\mu_W$. Then every observable equilibrium $(\delta,p_W,p_B)$ at $\mu_S$ is the schedule-and-balk equilibrium:
--   $$p_W=0,\qquad \delta=\delta^S_B=\frac{R}{C_D},\qquad p_B=p^S_B=\pi\Big(\frac{R}{C_D},\mu_S\Big).$$
--
--   When the walk-in hours are this short, the exogenous walk-ins alone make walking in worthless, so no strategic patient walks in and those not scheduling balk. In Proposition 6 this is the case where the strategic and triage models coincide.
--
--   **Formalization Note** $\underline\mu_W$ is a parameter with the hypothesis (15) (which forces $\lambda_E>0$); it is unique because $w$ is strictly increasing. The statement covers every equilibrium, not just the one Proposition 1 constructs. Parts 2–3 of Proposition 2 are not posed.
-- source:
--   Liu, van Jaarsveld, Wang, Xiao, Managing Outpatient Service with Strategic Walk-ins, SSRN 3558209 (version of 2022-07-05), p. 22, Proposition 2 (1); (15), p. 21; Regime SnB, p. 16 and Online Appendix p. 10, D.3

import Mathlib
import Definitions.Def_OutpatientWalkIn_Triage_Queue
import Definitions.Def_OutpatientWalkIn_Triage_Setting

namespace OutpatientWalkIn.Triage

theorem proposition_2_1 (M : Model) (hM : M.Standing) (μWl : ℝ) (hμWl : 0 < μWl)
    (h15 : M.R - M.CW * M.w (M.lamE / μWl) = 0) :
    ∀ μS ∈ Set.Ico 0 M.mu, M.mu - μS ≤ μWl → ∀ e : ObsStrategy, M.IsObsEq μS e →
      e.pW = 0 ∧ e.δ = M.R / M.CD ∧ e.pB = blockProb M.lam (M.R / M.CD) μS := by sorry

end OutpatientWalkIn.Triage
