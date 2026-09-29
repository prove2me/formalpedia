-- Prove2me | Theorems.Thm_PreorderADI_Correlation_threshold_quasiconvex
-- name    : PreorderADI.Correlation.threshold_quasiconvex
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:53:55.780095+00:00
-- url     : https://prove2.me/theorems/15d271c7-317b-4def-975f-f10fa818d449
-- title:
--   LEMMA 2(ii) — for z_L ≤ −λ_L/2, the threshold μ̃(ρ) is quasi-convex in ρ
-- statement:
--   Fix the model parameters under the standing assumptions, and suppose
--
--   $$
--   z_L \le -\frac{\lambda_L}{2}.
--   $$
--
--   Then the threshold $\tilde\mu(\rho)$ of (6) is quasi-convex in $\rho$ on $[0,1)$: for every level $t$, the set $\{\rho \in [0,1) : \tilde\mu(\rho) \le t\}$ is convex.
--
--   For very small margins the threshold, and with it the region where the preorder profit increases, is therefore first decreasing and then increasing in $\rho$.
--
--   **Formalization Note** Quasi-convexity is Mathlib's `QuasiconvexOn` (convex sublevel sets), the standard meaning. The standing assumptions include the added $c > 0$, $\mu_H, \mu_L, \sigma_L > 0$.
-- source:
--   Li and Zhang, Advance demand information, price discrimination, and preorder strategies, Manufacturing Service Oper. Management 15(1), 2013, p. 62, §4.1, LEMMA 2(ii)

import Mathlib
import Definitions.Def_PreorderADI_Correlation_Model

open MeasureTheory ProbabilityTheory

namespace PreorderADI.Correlation

theorem threshold_quasiconvex (P : Params) (hP : P.Standing)
    (hz : P.zL ≤ -(P.lamL / 2)) :
    QuasiconvexOn ℝ (Set.Ico (0:ℝ) 1) (threshold P) := by sorry

end PreorderADI.Correlation
