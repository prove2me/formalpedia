-- Prove2me | Theorems.Thm_TokenFinance_Statics_proposition_4
-- name    : TokenFinance.Statics.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T06:18:30.482833+00:00
-- url     : https://prove2.me/theorems/3756cc06-6acf-4b72-b82e-625102fd9b22
-- title:
--   Proposition 4, p. 25 — comparative statics of the optimal token pre-sale
-- statement:
--   Let $t$ be a positive pre-sale size satisfying the token break-even condition (16) for positive marginal cost $c$, positive set-up cost $C_0$, and demand intercept uniform on $(0,\theta)$. On positive-NPV projects, the unique such size is strictly increasing in $C_0$ and $c$ and strictly decreasing in $\theta$. In particular, whenever both endpoints satisfy (16),
--   $$C_0<C_0'\Longrightarrow t(c,C_0,\theta)<t(c,C_0',\theta),$$
--   $$c<c'\Longrightarrow t(c,C_0,\theta)<t(c',C_0,\theta),$$
--   $$\theta<\theta'\Longrightarrow t(c,C_0,\theta')<t(c,C_0,\theta).$$
--   This describes how the contract scales with financing need, production cost, and expected demand.
--
--   **Formalization Note** Lean compares all positive roots directly; uniqueness from the preceding milestone makes this equivalent to comparing the optimal roots. The positive-NPV condition is $C_0<(\theta-c)^3/(12\theta)$ from (3). For the cost comparison it is imposed at the higher cost $c'$, and for the demand comparison at the lower demand $\theta$; these imply positivity at the other endpoint.
-- source:
--   Malinova & Park, Tokenomics: When Tokens Beat Equity, SSRN 3286825 (version of June 1, 2023), p. 25 (PDF p. 26), Proposition 4; proof pp. 41–42 (PDF pp. 42–43)

import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting

namespace TokenFinance.Statics

theorem proposition_4 :
    (∀ c C0 C0' θ t t' : ℝ,
      0 < c → c < θ → 0 < C0 → C0 < C0' →
      C0' < (θ - c) ^ 3 / (12 * θ) →
      0 < t → TokenFinance.Debt.tokenBreakEven c C0 θ t →
      0 < t' → TokenFinance.Debt.tokenBreakEven c C0' θ t' → t < t') ∧
    (∀ c c' C0 θ t t' : ℝ,
      0 < c → c < c' → c' < θ → 0 < C0 →
      C0 < (θ - c') ^ 3 / (12 * θ) →
      0 < t → TokenFinance.Debt.tokenBreakEven c C0 θ t →
      0 < t' → TokenFinance.Debt.tokenBreakEven c' C0 θ t' → t < t') ∧
    (∀ c C0 θ θ' t t' : ℝ,
      0 < c → c < θ → θ < θ' → 0 < C0 →
      C0 < (θ - c) ^ 3 / (12 * θ) →
      0 < t → TokenFinance.Debt.tokenBreakEven c C0 θ t →
      0 < t' → TokenFinance.Debt.tokenBreakEven c C0 θ' t' → t' < t) := by sorry

end TokenFinance.Statics
