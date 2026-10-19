-- Prove2me | Theorems.Thm_TokenFinance_Debt_eq_3
-- name    : TokenFinance.Debt.eq_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T04:29:43.851654+00:00
-- url     : https://prove2.me/theorems/7815d422-dbc6-4bd0-9722-f665998f34d9
-- title:
--   (3), p. 14 — the expected monopoly profit is (θ − c)³/(12θ), so NPV = (θ − c)³/(12θ) − C₀
-- statement:
--   Let the demand intercept $x$ be uniform on $(0,\theta)$, let $0 < c < \theta$ be the marginal cost, and let $C_0$ be the set-up cost. The monopoly profit is $\pi^m(x) = (x-c)^2/4$ for $x \ge c$ and $0$ for $x < c$. Then the venture's expected net present value has the closed form
--
--   $$
--   \mathrm{NPV} = \int_0^\theta \frac{1}{\theta}\,\pi^m(x)\,dx - C_0 = \int_c^\theta \frac1\theta\left(\frac{x-c}{2}\right)^2 dx - C_0 = \frac{1}{12}\,\frac{(\theta-c)^3}{\theta} - C_0 .
--   $$
--
--   This identity links the NPV, defined as an expectation of realized profits, to the cubic expression in which the paper's break-even conditions are solved; it is used to evaluate the left-hand side of (33) at $\delta = 1$.
--
--   **Formalization Note** `npv c C0 θ` is defined as the integral $\frac1\theta\int_0^\theta \pi^m$; the hypothesis $0 < c$ is the paper's standing "positive marginal cost" assumption (the identity also needs $c \ge 0$, since for $c<0$ the integrand is positive on all of $(0,\theta)$).
-- source:
--   Malinova & Park, Tokenomics: When Tokens Beat Equity, SSRN 3286825 (version of June 1, 2023), p. 14 (PDF p. 15), (3)

import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting

namespace TokenFinance.Debt
theorem eq_3 (c C0 θ : ℝ) (hc : 0 < c) (hcθ : c < θ) :
    npv c C0 θ = (θ - c) ^ 3 / (12 * θ) - C0 := by sorry
end TokenFinance.Debt
