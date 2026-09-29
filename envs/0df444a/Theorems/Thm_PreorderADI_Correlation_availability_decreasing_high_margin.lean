-- Prove2me | Theorems.Thm_PreorderADI_Correlation_availability_decreasing_high_margin
-- name    : PreorderADI.Correlation.availability_decreasing_high_margin
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T14:51:51.776052+00:00
-- url     : https://prove2.me/theorems/8d000e40-a0a7-4ab3-a954-311dcfbba4b0
-- title:
--   LEMMA 1(ii) — for v_L ≥ 2c, z_L ≥ 0 and the availability ξ is decreasing in ρ
-- statement:
--   Fix the model parameters under the standing assumptions, and suppose the low-type margin is large:
--
--   $$
--   v_L \ge 2c.
--   $$
--
--   Then $z_L \ge 0$, and the availability belief $\xi(\rho)$ of (3) is non-increasing in $\rho$ on $[0,1)$. If moreover $v_L > 2c$, then $\xi$ is strictly decreasing in $\rho$ on $[0,1)$.
--
--   With a large margin the seller orders above the conditional mean, so more accurate information (a smaller conditional variance) lowers the order quantity and the product availability.
--
--   **Formalization Note** "Decreasing" is read as non-increasing (`AntitoneOn`) because at $v_L = 2c$ one has $z_L = 0$ and $\xi$ is constant in $\rho$; the strict version is stated under $v_L > 2c$. The standing assumptions include the added $c > 0$, $\mu_H, \mu_L, \sigma_L > 0$.
-- source:
--   Li and Zhang, Advance demand information, price discrimination, and preorder strategies, Manufacturing Service Oper. Management 15(1), 2013, p. 62, §4.1, LEMMA 1(ii)

import Mathlib
import Definitions.Def_PreorderADI_Correlation_Model

open MeasureTheory ProbabilityTheory

namespace PreorderADI.Correlation

theorem availability_decreasing_high_margin (P : Params) (hP : P.Standing)
    (h2c : 2 * P.c ≤ P.vL) :
    0 ≤ P.zL ∧ AntitoneOn (availability P) (Set.Ico (0:ℝ) 1) ∧
      (2 * P.c < P.vL → StrictAntiOn (availability P) (Set.Ico (0:ℝ) 1)) := by sorry

end PreorderADI.Correlation
