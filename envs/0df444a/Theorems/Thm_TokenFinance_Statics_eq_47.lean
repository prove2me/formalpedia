-- Prove2me | Theorems.Thm_TokenFinance_Statics_eq_47
-- name    : TokenFinance.Statics.eq_47
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T06:18:26.193815+00:00
-- url     : https://prove2.me/theorems/506e9206-8e8d-4ca2-89e5-ae48d99b87fe
-- title:
--   Equation (47), p. 42 — the demand partial derivative decreases in the pre-sale size
-- statement:
--   Let $0<c<\theta$. The expression for $\partial F/\partial\theta$ in (46) is zero at $t=0$. For $t>-c$, its derivative in $t$ is
--   $$-\frac{c}{3}\frac{(\theta-c-2t)(2\theta+c+2t)}{(c+t)\theta^2}-\frac{c}{12}\frac{(\theta-c-2t)^2(2\theta-c)}{(c+t)^2\theta^2}.$$
--   This derivative is strictly negative for $0\le t<(\theta-c)/2$. It accounts for the strict sign in (46).
--
--   **Formalization Note** The derivative formula is stated on its full differentiability domain $t>-c$; its sign is asserted only in the economic interval.
-- source:
--   Malinova & Park, Tokenomics: When Tokens Beat Equity, SSRN 3286825 (version of June 1, 2023), p. 42 (PDF p. 43), Appendix A, proof of Proposition 4, (47)

import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting

namespace TokenFinance.Statics

theorem eq_47 (c θ : ℝ) (hc : 0 < c) (hcθ : c < θ) :
    (c / 3 * ((θ - c) / 2 - 0) ^ 2 * (2 * θ + c + 2 * 0) /
        ((c + 0) * θ ^ 2) -
      (θ - c) ^ 2 * (2 * θ + c) / (12 * θ ^ 2) = 0) ∧
    (∀ t : ℝ, -c < t →
      HasDerivAt
        (fun s : ℝ => c / 3 * ((θ - c) / 2 - s) ^ 2 * (2 * θ + c + 2 * s) /
            ((c + s) * θ ^ 2) -
          (θ - c) ^ 2 * (2 * θ + c) / (12 * θ ^ 2))
        (-(c / 3) * (θ - c - 2 * t) * (2 * θ + c + 2 * t) /
            ((c + t) * θ ^ 2) -
          c / 12 * (θ - c - 2 * t) ^ 2 * (2 * θ - c) /
            ((c + t) ^ 2 * θ ^ 2)) t) ∧
    (∀ t : ℝ, 0 ≤ t → t < (θ - c) / 2 →
      (-(c / 3) * (θ - c - 2 * t) * (2 * θ + c + 2 * t) /
          ((c + t) * θ ^ 2) -
        c / 12 * (θ - c - 2 * t) ^ 2 * (2 * θ - c) /
          ((c + t) ^ 2 * θ ^ 2)) < 0) := by sorry

end TokenFinance.Statics
