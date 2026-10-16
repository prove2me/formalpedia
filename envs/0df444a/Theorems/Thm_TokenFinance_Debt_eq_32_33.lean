-- Prove2me | Theorems.Thm_TokenFinance_Debt_eq_32_33
-- name    : TokenFinance.Debt.eq_32_33
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T04:29:38.077541+00:00
-- url     : https://prove2.me/theorems/a27835f2-e9e0-4183-8bee-12646c75a53f
-- title:
--   (32)–(33), Appendix A, pp. 38–39 — with D = (θ − c)²δ²/4, the break-even condition (7) becomes (θ − c)³/(12θ)(−2δ³ + 3δ²) − C₀ = 0
-- statement:
--   Let $0 < c < \theta$, let $C_0$ be the set-up cost and $x \sim U(0,\theta)$ the demand intercept. Parametrize a debt repayment by $\delta = 2\sqrt D/(\theta - c)$, that is $D = (\theta-c)^2\delta^2/4$, and let $0 \le \delta \le 1$. The investors receive $\min\{\pi^m(x), D\}$ at demand $x$. Then the investors' expected receipts minus $C_0$ (the left-hand side of (7) minus $C_0$) equals both the left-hand side of (32),
--
--   $$
--   \int_c^{c+\delta(\theta-c)} \frac1\theta\,\frac{(x-c)^2}{4}\,dx + \int_{c+\delta(\theta-c)}^{\theta} \frac1\theta\,\frac{(\theta-c)^2\delta^2}{4}\,dx - C_0 ,
--   $$
--
--   and the left-hand side of (33),
--
--   $$
--   \frac{(\theta-c)^3}{12\theta}\left(-2\delta^3 + 3\delta^2\right) - C_0 .
--   $$
--
--   So the investors' break-even condition (7) for $D$ is the cubic equation (33) in $\delta$.
--
--   **Formalization Note** The left-hand side of (7) is `expect θ (debtInv c D)` with `debtInv c D x = min (π^m(x)) D`, the investors' realized repayment in the three regimes of p. 16; the split integral (32) is a consequence, stated here as the first conjunct. The restriction $\delta \le 1$ (from the paper: $D$ cannot exceed $\pi^m(\theta)$) keeps the limits of (32) in order.
-- source:
--   Malinova & Park, Tokenomics: When Tokens Beat Equity, SSRN 3286825 (version of June 1, 2023), pp. 37–39 (PDF pp. 38–40), Appendix A, proof of Proposition 2, (32)–(33)

import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting

namespace TokenFinance.Debt
theorem eq_32_33 (c C0 θ δ : ℝ) (hc : 0 < c) (hcθ : c < θ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    expect θ (debtInv c ((θ - c) ^ 2 * δ ^ 2 / 4)) - C0 =
        (∫ x in c..(c + δ * (θ - c)), 1 / θ * ((x - c) ^ 2 / 4)) +
          (∫ _x in (c + δ * (θ - c))..θ, 1 / θ * ((θ - c) ^ 2 * δ ^ 2 / 4)) - C0 ∧
      expect θ (debtInv c ((θ - c) ^ 2 * δ ^ 2 / 4)) - C0 =
        (θ - c) ^ 3 / (12 * θ) * (-2 * δ ^ 3 + 3 * δ ^ 2) - C0 := by sorry
end TokenFinance.Debt
