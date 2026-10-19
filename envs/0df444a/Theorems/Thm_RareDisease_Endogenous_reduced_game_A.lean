-- Prove2me | Theorems.Thm_RareDisease_Endogenous_reduced_game_A
-- name    : RareDisease.Endogenous.reduced_game_A
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T08:07:16.103564+00:00
-- url     : https://prove2.me/theorems/f2dec805-358d-46f0-a9ea-671f7112cff4
-- title:
--   Equation (13) — sales-based welfare and budget after best response
-- statement:
--   Let $k>0$ and $\alpha,\beta\in[0,1)$. For every manufacturer best response $(p,e)$ in the sales-based scheme, the resulting patient welfare $W_A$ and government spending $M_A$ are
--   $$
--   W_A=\frac{1}{64(1-\alpha)k(1-\beta)},\qquad
--   M_A=\frac{\alpha}{64(1-\alpha)^2k(1-\beta)^2}+\frac{\beta}{32(1-\alpha)k(1-\beta)^2}.
--   $$
--   These identities are the objective and budget expression in the government's reduced problem (13).
--
--   **Formalization Note** Welfare and spending are defined from equations (2) and (5) and evaluated at a member of the best-response set; neither reduced identity is built into the game definition.
-- source:
--   Olsder, Martagan, Tang, Improving Access to Rare Disease Treatments: Optimal Subsidies, Pricing, and Payment, SSRN working paper 3481150 (version of 2019-11-13), p. 12, §4.1, after (12), equation (13)

import Mathlib
import Definitions.Def_RareDisease_Endogenous_Setting

namespace RareDisease.Endogenous

/-- Equation (13), p. 12: welfare and spending after the sales-based best response. -/
theorem reduced_game_A (k α β : ℝ) (hk : 0 < k) (hpolicy : IsPolicy α β)
    (x : ℝ × ℝ) (hx : x ∈ BRA k α β) :
    welfareA β x.1 x.2 = 1 / (64 * (1 - α) * k * (1 - β)) ∧
    spendA k α β x.1 x.2 =
      α / (64 * (1 - α) ^ 2 * k * (1 - β) ^ 2) +
      β / (32 * (1 - α) * k * (1 - β) ^ 2) := by sorry

end RareDisease.Endogenous
