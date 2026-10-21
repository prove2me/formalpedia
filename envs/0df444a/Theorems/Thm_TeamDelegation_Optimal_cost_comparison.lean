-- Prove2me | Theorems.Thm_TeamDelegation_Optimal_cost_comparison
-- name    : TeamDelegation.Optimal.cost_comparison
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:16:21.812521+00:00
-- url     : https://prove2.me/theorems/a02350a6-c437-4ada-968c-ecfbaabcc3dc
-- title:
--   Equations (73)–(74): when delegation costs less
-- statement:
--   When $\Delta_A\le\Delta_A^{\mathrm{crit}}$, the first branch of A's delegated bonus applies. Under the standing assumptions and Assumption 1, total delegated success bonuses are strictly smaller than the optimal centralised total exactly when
--
--   $$w_A^{\mathrm{del}}+w_B^{\mathrm{del}}<2w^{\mathrm{cent}}
--   \quad\Longleftrightarrow\quad
--   \Delta_A+\Delta_B<\Delta_{\mathrm{sum}}^*,\qquad
--   \Delta_{\mathrm{sum}}^*=\frac{2e(p_0-q_0)}{p_2-(1-\delta)p_1-\delta p_0}.$$
--
--   Because the desired outcome has success probability $p_2$ under both organisations, this is also the principal's strict wage-cost comparison.
-- source:
--   Upton, Implicit Incentives and Delegation in Teams, TRR 266 Working Paper No. 67 (SSRN 3991736, 17 Dec 2021), p. 39 (PDF 40), equations (73)–(74)

import Mathlib
import Definitions.Def_TeamDelegation_Optimal_Model

namespace TeamDelegation.Optimal

/-- Equations (73)–(74), p. 39: in the first branch of A's wage,
delegation's total bonus is smaller exactly below the aggregate threshold. -/
theorem cost_comparison (P : Params) (hS : P.Standing)
    (hA1 : P.Assumption1) (ΔA ΔB : ℝ)
    (hbranch : ΔA ≤ DeltaCritA P) :
    wdelA P ΔA + wdelB P ΔB < 2 * wcent P ↔
      ΔA + ΔB < DeltaStarSum P := by sorry

end TeamDelegation.Optimal
