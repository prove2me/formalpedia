-- Prove2me | Theorems.Thm_TokenFinance_Debt_eq_8
-- name    : TokenFinance.Debt.eq_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T04:29:47.987985+00:00
-- url     : https://prove2.me/theorems/118b7d08-becc-42fa-8265-e925cc7719b4
-- title:
--   (8), p. 16 — at a break-even repayment D the entrepreneur's expected profit under debt equals the NPV
-- statement:
--   Let $0 < c < \theta$, let $x \sim U(0,\theta)$, and let $D \ge 0$ be a repayment at which the debtholders break even, i.e. (7) holds:
--
--   $$
--   \mathsf E\big[\min\{\pi^m(x), D\}\big] = C_0 .
--   $$
--
--   Then the entrepreneur, who keeps $\max\{\pi^m(x) - D, 0\}$, earns the venture's NPV in expectation:
--
--   $$
--   \mathsf E\big[\max\{\pi^m(x) - D, 0\}\big] = \mathsf E[\pi^m(x)] - C_0 = \mathrm{NPV} .
--   $$
--
--   Moreover, when the solvency threshold $c + 2\sqrt D$ does not exceed $\theta$, this expectation equals the left-hand side of (8), $\int_{c+2\sqrt D}^{\theta} \frac1\theta\big(\pi^m(x) - D\big)\,dx$ with $\pi^m(x) = (x-c)^2/4$.
--
--   As under equity financing, debt financing leaves the entrepreneur the entire surplus of the project; the result is the second half of Proposition 2.
--
--   **Formalization Note** The entrepreneur's realized payoff is `debtEnt c D x = max (π^m(x) − D) 0`; the split integral of (8) is stated only under $c + 2\sqrt D \le \theta$, where its limits are in order.
-- source:
--   Malinova & Park, Tokenomics: When Tokens Beat Equity, SSRN 3286825 (version of June 1, 2023), p. 16 (PDF p. 17), (8)

import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting

namespace TokenFinance.Debt
theorem eq_8 (c C0 θ D : ℝ) (hc : 0 < c) (hcθ : c < θ) (hD : 0 ≤ D)
    (h7 : expect θ (debtInv c D) = C0) :
    expect θ (debtEnt c D) = npv c C0 θ ∧
      (c + 2 * Real.sqrt D ≤ θ →
        expect θ (debtEnt c D) = ∫ x in (c + 2 * Real.sqrt D)..θ, 1 / θ * ((x - c) ^ 2 / 4 - D)) := by sorry
end TokenFinance.Debt
