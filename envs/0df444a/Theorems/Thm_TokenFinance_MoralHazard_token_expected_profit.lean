-- Prove2me | Theorems.Thm_TokenFinance_MoralHazard_token_expected_profit
-- name    : TokenFinance.MoralHazard.token_expected_profit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T06:18:42.243876+00:00
-- url     : https://prove2.me/theorems/54234c27-2d13-44a6-a7f5-ab83423cde2f
-- title:
--   p. 31 — the token entrepreneur's expected profit is c/(c+t)·2/(3θ)·((θ−c)/2−t)³ if θ ≥ c+2t and 0 otherwise
-- statement:
--   Let $c>0$, $t>0$, $\theta>0$, and let the entrepreneur under the token contract with pre-sale $t$ produce the monopoly quantity $q^m(x)$. Her expected profit under demand uniform on $(0,\theta)$ is
--   $$\mathbb E_\theta\big[\pi^e_t(x,q^m(x))\big]=\begin{cases}\dfrac{c}{c+t}\,\dfrac{2}{3\theta}\Big(\dfrac{\theta-c}{2}-t\Big)^3, & c+2t\le\theta,\\[2mm] 0, & \theta\le c+2t.\end{cases}$$
--
--   With $\theta=\theta_h$ this is the left-hand side of (26); with $\theta=\theta_l$ it is the no-effort profit on the right of (27), and it vanishes when $\theta_l\le c+2t$, where the entrepreneur always exerts effort.
-- source:
--   Malinova & Park, Tokenomics: When Tokens Beat Equity, SSRN 3286825 (version of June 1, 2023), p. 31 (PDF 32), the paragraph after (26)

import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting

namespace TokenFinance.MoralHazard

/-- p. 31: under the token contract with pre-sale `t` and monopoly output, the entrepreneur's
expected profit under `U(0, θ)` is `c/(c+t) · 2/(3θ) · ((θ − c)/2 − t)³` when `c + 2t ≤ θ`,
and `0` when `θ ≤ c + 2t`. -/
theorem token_expected_profit (c t θ : ℝ) (hc : 0 < c) (ht : 0 < t) (hθ : 0 < θ) :
    (c + 2 * t ≤ θ →
      TokenFinance.Debt.expect θ (fun x => TokenFinance.Debt.tokEnt c t x (TokenFinance.Debt.qm c x)) =
        c / (c + t) * (2 / (3 * θ)) * ((θ - c) / 2 - t) ^ 3) ∧
    (θ ≤ c + 2 * t → TokenFinance.Debt.expect θ (fun x => TokenFinance.Debt.tokEnt c t x (TokenFinance.Debt.qm c x)) = 0) := by sorry

end TokenFinance.MoralHazard
