-- Prove2me | Theorems.Thm_OutpatientWalkIn_Triage_walkin_intensity_SnW
-- name    : OutpatientWalkIn.Triage.walkin_intensity_SnW
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:05:57.116317+00:00
-- url     : https://prove2.me/theorems/5b06bccb-e1ba-4cf9-be62-0ff383baa443
-- title:
--   Proof of Proposition 6 (2)(a), Online App. p. 36 — in Regime SnW, (λ^{s,t*}_W + λ_E)/µ_W ≤ λ_E/µ̲_W
-- statement:
--   Assume the standing assumptions and let $\underline\mu_W>0$ satisfy (15), $R-C_W\,w(\lambda_E/\underline\mu_W)=0$. Let $\mu_S\in[0,\mu)$, $\mu_W=\mu-\mu_S$, and let $(\delta,p_W,p_B)$ be an observable equilibrium at $\mu_S$ in which nobody balks, $p_B=0$ (Regime SnW). Then the walk-in traffic intensity satisfies
--   $$\frac{\lambda p_W+\lambda_E}{\mu_W}\le\frac{\lambda_E}{\underline\mu_W}.$$
--
--   Since walking in must be worth at least balking, the walk-in intensity cannot exceed the intensity at which the exogenous walk-ins alone exhaust the reward. The proof of part 2 of Proposition 6 uses this bound to control the strategic model's overtime.
--
--   **Formalization Note** The paper conditions on "$\mu\ge\overline\mu_O$, i.e., the equilibrium … is in SnW regime"; the regime depends on the allocation, so the statement is conditioned on the regime itself ($p_B=0$). The strategic walk-in rate $\lambda^{s,t*}_W$ is $\lambda p_W$.
-- source:
--   Liu, van Jaarsveld, Wang, Xiao, Managing Outpatient Service with Strategic Walk-ins, SSRN 3558209 (version of 2022-07-05), Online Appendix p. 36, proof of Proposition 6 (2), case (a)

import Mathlib
import Definitions.Def_OutpatientWalkIn_Triage_Queue
import Definitions.Def_OutpatientWalkIn_Triage_Setting

namespace OutpatientWalkIn.Triage

theorem walkin_intensity_SnW (M : Model) (hM : M.Standing) (μWl : ℝ) (hμWl : 0 < μWl)
    (h15 : M.R - M.CW * M.w (M.lamE / μWl) = 0) :
    ∀ μS ∈ Set.Ico 0 M.mu, ∀ e : ObsStrategy, M.IsObsEq μS e → e.pB = 0 →
      (M.lam * e.pW + M.lamE) / (M.mu - μS) ≤ M.lamE / μWl := by sorry

end OutpatientWalkIn.Triage
