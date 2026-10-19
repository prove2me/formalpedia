-- Prove2me | Theorems.Thm_RareDisease_Endogenous_reduced_game_B
-- name    : RareDisease.Endogenous.reduced_game_B
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T08:07:18.24798+00:00
-- url     : https://prove2.me/theorems/9c3334bb-49f9-4f61-ab0a-19e5b61730e0
-- title:
--   Equation (16) — outcome-based welfare and budget after best response
-- statement:
--   Let $k>0$ and $\alpha,\beta\in[0,1)$. At every manufacturer best response $(p,e)$ in the outcome-based scheme, patient welfare $W_B$ and government spending $M_B$ satisfy
--   $$
--   W_B=\frac{1}{64(1-\alpha)k(1-\beta)},\qquad
--   M_B=\frac{\alpha}{64(1-\alpha)^2k(1-\beta)^2}+\frac{\beta}{32(1-\alpha)k(1-\beta)^2}.
--   $$
--   These are the same reduced objective and budget expression as in Setting (1A), which is the comparison made at equation (16).
--
--   **Formalization Note** The expressions are consequences of equations (7), (10), (14), and (15) at a best response, not definitions of the government's problem.
-- source:
--   Olsder, Martagan, Tang, Improving Access to Rare Disease Treatments: Optimal Subsidies, Pricing, and Payment, SSRN working paper 3481150 (version of 2019-11-13), p. 13, §4.2, equation (16)

import Mathlib
import Definitions.Def_RareDisease_Endogenous_Setting

namespace RareDisease.Endogenous

/-- Equation (16), p. 13: welfare and spending after the outcome-based best response. -/
theorem reduced_game_B (k α β : ℝ) (hk : 0 < k) (hpolicy : IsPolicy α β)
    (x : ℝ × ℝ) (hx : x ∈ BRB k α β) :
    welfareB β x.1 x.2 = 1 / (64 * (1 - α) * k * (1 - β)) ∧
    spendB k α β x.1 x.2 =
      α / (64 * (1 - α) ^ 2 * k * (1 - β) ^ 2) +
      β / (32 * (1 - α) * k * (1 - β) ^ 2) := by sorry

end RareDisease.Endogenous
