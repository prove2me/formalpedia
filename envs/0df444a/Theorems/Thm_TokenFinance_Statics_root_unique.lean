-- Prove2me | Theorems.Thm_TokenFinance_Statics_root_unique
-- name    : TokenFinance.Statics.root_unique
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T06:18:25.689685+00:00
-- url     : https://prove2.me/theorems/70541b98-18ba-4171-9ddc-d1878909c744
-- title:
--   Proof of Proposition 4, p. 41 — unique positive root of (41)
-- statement:
--   Let $c>0$ be the marginal cost, $\theta>c$ the upper demand intercept, and $C_0>0$ the set-up cost. Suppose $C_0<(\theta-c)^3/(12\theta)$, so the project's net present value is positive. There is exactly one positive pre-sale size $t$ satisfying the token break-even equation (16), and it lies below the maximal monopoly quantity:
--   $$0<t<\frac{\theta-c}{2},\qquad \frac{c}{c+t}\frac{2}{3\theta}\left(\frac{\theta-c}{2}-t\right)^3=\frac{(\theta-c)^3}{12\theta}-C_0.$$
--   This identifies the contract size whose movement is studied in Proposition 4.
--
--   **Formalization Note** The positive-NPV condition is written using the closed form (3). The text following (41) has a sign slip: $F$ decreases, rather than increases, in $t$.
-- source:
--   Malinova & Park, Tokenomics: When Tokens Beat Equity, SSRN 3286825 (version of June 1, 2023), p. 41 (PDF p. 42), Appendix A, proof of Proposition 4, (41), with proof of Proposition 3, pp. 40–41 (PDF pp. 41–42)

import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting

namespace TokenFinance.Statics

theorem root_unique (c C0 θ : ℝ) (hc : 0 < c) (hcθ : c < θ)
    (hC0 : 0 < C0) (hNPV : C0 < (θ - c) ^ 3 / (12 * θ)) :
    (∃! t : ℝ, 0 < t ∧ TokenFinance.Debt.tokenBreakEven c C0 θ t) ∧
      (∀ t : ℝ, 0 < t → TokenFinance.Debt.tokenBreakEven c C0 θ t → t < (θ - c) / 2) := by sorry

end TokenFinance.Statics
