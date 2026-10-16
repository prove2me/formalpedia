-- Prove2me | Theorems.Thm_TokenFinance_Debt_proposition_2
-- name    : TokenFinance.Debt.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T04:29:41.626806+00:00
-- url     : https://prove2.me/theorems/534745e4-7f66-4085-a46b-0a4ef5768026
-- title:
--   Proposition 2, p. 17 — debt finances every positive-NPV project: a unique break-even repayment D ∈ (C₀, (θ − c)²/4), and the entrepreneur earns the NPV
-- statement:
--   **Proposition 2 (Debt Financing).** An entrepreneur pays a set-up cost $C_0 > 0$ and becomes a monopolist with marginal cost $c$, facing inverse demand $p(q) = x - q$ with $x \sim U(0,\theta)$, $0 < c < \theta$. Her monopoly profit at demand $x$ is $\pi^m(x) = (x-c)^2/4$ for $x \ge c$ and $0$ otherwise. Under debt with promised repayment $D$, investors receive $\min\{\pi^m(x), D\}$ and the entrepreneur keeps $\max\{\pi^m(x)-D, 0\}$. Suppose the project has positive NPV, $\mathsf E[\pi^m(x)] - C_0 > 0$. Then
--
--   1. there is exactly one repayment $D \ge 0$ at which investors break even in expectation,
--   $$
--   \mathsf E\big[\min\{\pi^m(x), D\}\big] = C_0 \qquad (7);
--   $$
--   2. that repayment satisfies $C_0 < D < (\theta-c)^2/4 = \pi^m(\theta)$, and the entrepreneur earns the project's expected NPV:
--   $$
--   \mathsf E\big[\max\{\pi^m(x)-D,0\}\big] = \mathrm{NPV}.
--   $$
--
--   In words: all positive-NPV projects can be financed by debt, the break-even repayment is unique and lies strictly between the amount borrowed and the largest possible monopoly profit, and debt, like equity, leaves the entrepreneur the full NPV.
--
--   **Formalization Note** Expectations are integrals of the realized payoffs (`expect`, `debtInv`, `debtEnt`); neither the NPV nor (7) is written in closed form. Uniqueness is asserted over all $D \ge 0$, which implies the paper's uniqueness in $(C_0, (\theta-c)^2/4)$. $0 < c$ is the paper's standing "positive marginal cost" assumption, kept for uniformity of the series.
-- source:
--   Malinova & Park, Tokenomics: When Tokens Beat Equity, SSRN 3286825 (version of June 1, 2023), p. 17 (PDF p. 18), Proposition 2, with (7) on p. 16 and the proof in Appendix A, pp. 37–39

import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting

namespace TokenFinance.Debt
theorem proposition_2 (c C0 θ : ℝ) (hc : 0 < c) (hcθ : c < θ) (hC0 : 0 < C0)
    (hnpv : 0 < npv c C0 θ) :
    (∃! D : ℝ, 0 ≤ D ∧ expect θ (debtInv c D) = C0) ∧
      ∀ D : ℝ, 0 ≤ D → expect θ (debtInv c D) = C0 →
        C0 < D ∧ D < (θ - c) ^ 2 / 4 ∧ expect θ (debtEnt c D) = npv c C0 θ := by sorry
end TokenFinance.Debt
