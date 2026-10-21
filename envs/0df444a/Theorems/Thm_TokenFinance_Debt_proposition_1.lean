-- Prove2me | Theorems.Thm_TokenFinance_Debt_proposition_1
-- name    : TokenFinance.Debt.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T04:29:40.560781+00:00
-- url     : https://prove2.me/theorems/5d8165bd-76e0-4bb7-affb-462d9d5e09a4
-- title:
--   Proposition 1, p. 15 — equity finances every positive-NPV project: α_s = 12θC₀/(θ − c)³ ∈ (0, 1), and the entrepreneur earns the NPV
-- statement:
--   **Proposition 1 (Equity Financing).** Let $0 < c < \theta$ and $C_0 > 0$, with demand intercept $x \sim U(0,\theta)$, and suppose the project has positive NPV. Let $\alpha_s$ be the investors' equity share defined by the break-even condition (5), $\alpha_s\,\mathsf E[\pi^m(x)] = C_0$. Then
--
--   1. $0 < \alpha_s < 1$;
--   2. $\alpha_s = \dfrac{12\,\theta\,C_0}{(\theta-c)^3}$;
--   3. the investors break even: $\alpha_s\,\mathsf E[\pi^m(x)] = C_0$;
--   4. the entrepreneur earns the venture's expected NPV: $(1-\alpha_s)\,\mathsf E[\pi^m(x)] = \mathrm{NPV}$.
--
--   Equity financing does not distort the monopoly output, so every positive-NPV project can be financed by equity; this is the benchmark against which debt and token financing are compared.
--
--   **Formalization Note** `equityShare c C0 θ` is $C_0/\mathsf E[\pi^m]$ with the expectation an integral; the closed form (5) is part of the conclusion. $0 < c$ is the paper's standing assumption.
-- source:
--   Malinova & Park, Tokenomics: When Tokens Beat Equity, SSRN 3286825 (version of June 1, 2023), p. 15 (PDF p. 16), Proposition 1 and (5)

import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting

namespace TokenFinance.Debt
theorem proposition_1 (c C0 θ : ℝ) (hc : 0 < c) (hcθ : c < θ) (hC0 : 0 < C0)
    (hnpv : 0 < npv c C0 θ) :
    0 < equityShare c C0 θ ∧ equityShare c C0 θ < 1 ∧
      equityShare c C0 θ = 12 * θ * C0 / (θ - c) ^ 3 ∧
      equityShare c C0 θ * expect θ (pim c) = C0 ∧
      (1 - equityShare c C0 θ) * expect θ (pim c) = npv c C0 θ := by sorry
end TokenFinance.Debt
