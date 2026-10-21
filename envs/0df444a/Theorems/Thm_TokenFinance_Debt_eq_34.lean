-- Prove2me | Theorems.Thm_TokenFinance_Debt_eq_34
-- name    : TokenFinance.Debt.eq_34
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T04:29:46.663019+00:00
-- url     : https://prove2.me/theorems/0f0ba5cf-a249-4a1a-b81e-dc7f9192fedb
-- title:
--   (34), p. 39 — the break-even repayment satisfies D = C₀ · θ/(θ − c) · 3/(3 − 2δ) > C₀
-- statement:
--   Let $0 < c < \theta$, $C_0 > 0$, and let $\delta \in (0,1)$ solve (33),
--
--   $$
--   \frac{(\theta-c)^3}{12\theta}\left(-2\delta^3+3\delta^2\right) - C_0 = 0 .
--   $$
--
--   Then the corresponding repayment $D = (\theta-c)^2\delta^2/4$ satisfies
--
--   $$
--   D = \frac{(\theta-c)^2\delta^2}{4} = C_0 \times \frac{\theta}{\theta-c} \times \frac{3}{3-2\delta} > C_0 .
--   $$
--
--   The inequality holds because both fractions on the right exceed $1$. It shows that the debt repayment strictly exceeds the amount borrowed: investors are compensated for the states in which the venture cannot repay in full.
-- source:
--   Malinova & Park, Tokenomics: When Tokens Beat Equity, SSRN 3286825 (version of June 1, 2023), p. 39 (PDF p. 40), Appendix A, proof of Proposition 2, (34)

import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting

namespace TokenFinance.Debt
theorem eq_34 (c C0 θ δ : ℝ) (hc : 0 < c) (hcθ : c < θ) (hC0 : 0 < C0)
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (h33 : (θ - c) ^ 3 / (12 * θ) * (-2 * δ ^ 3 + 3 * δ ^ 2) - C0 = 0) :
    (θ - c) ^ 2 * δ ^ 2 / 4 = C0 * (θ / (θ - c)) * (3 / (3 - 2 * δ)) ∧
      C0 < (θ - c) ^ 2 * δ ^ 2 / 4 := by sorry
end TokenFinance.Debt
