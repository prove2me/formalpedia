-- Prove2me | Theorems.Thm_StrongWeakEq_TwoState_display_4_5
-- name    : StrongWeakEq.TwoState.display_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T23:32:48.112071+00:00
-- url     : https://prove2.me/theorems/6dccedca-7fd8-4062-afa0-2eedc3f9748d
-- title:
--   (4.5), (4.6), (4.8), p. 12 — Γ^{Q*}(Q₁), Γ^{Q*}(Q₂) and Λ^{Q*}(2, Q) in the two-state model
-- statement:
--   In the two-state model of §4 (with $\lambda\in(0,1)$, $\rho,\rho'\ge0$, arbitrary $g_1,g_2$), let $Q\sim(a,b)$ and $Q^*\sim(a^*,b^*)$ with $a,b,a^*,b^*\ge0$, and abbreviate $F_i=F(i,Q^*)$, $G_i=G(i,Q^*)$. Then
--   $$
--   \Gamma^{(a^*,b^*)}_1(a):=\Gamma^{Q^*}(Q_1)=g_1(a)-a\,(F_1-F_2), \tag{4.5}
--   $$
--   $$
--   \Gamma^{(a^*,b^*)}_2(b):=\Gamma^{Q^*}(Q_2)=g_2(b)+b\,(F_1-F_2), \tag{4.6}
--   $$
--   $$
--   \Lambda^{(a^*,b^*)}_2(a,b):=\Lambda^{Q^*}(2,Q)=2b\,(G_1-G_2)+b\,(g_1(a)-g_2(b))-(\rho\lambda+\rho'(1-\lambda))\,g_2(b)-(b^2+ab)(F_1-F_2). \tag{4.8}
--   $$
--
--   These are the specializations of (3.7) and (3.17) that reduce the first- and second-order tests to one-variable functions in Example 4.3.
--
--   **Formalization Note** State 1 is `0 : Fin 2`, state 2 is `1 : Fin 2`; $Q_1$ is the row `gen a b 0` $=(-a,a)$ and $Q_2$ the row `gen a b 1` $=(b,-b)$. The constant $\rho\lambda+\rho'(1-\lambda)=-\delta'(0)$ comes from $f_t(0,2,Q_2)$, and $\delta(0)=1$. These identities are algebra on the definitions of $\Gamma$ and $\Lambda$, so the page's own range $\rho,\rho'\ge0$ is kept (unlike (4.3)–(4.4), no integral is evaluated here).
-- source:
--   Huang & Zhou, Strong and Weak Equilibria for Time-Inconsistent Stochastic Control in Continuous Time, arXiv:1809.09243v3, p. 12, (4.5), (4.6), (4.8)

import Mathlib
import Definitions.Def_StrongWeakEq_Existence_Model
import Definitions.Def_StrongWeakEq_Existence_SecondOrder
import Definitions.Def_StrongWeakEq_TwoState_TwoStateModel

namespace StrongWeakEq.TwoState

/-- (4.5), (4.6), (4.8), p. 12: for `Q ∼ (a, b)` and `Q* ∼ (a*, b*)`, with `F_i = F(i, Q*)` and
`G_i = G(i, Q*)`: `Γ^{Q*}(Q₁) = g₁(a) − a (F₁ − F₂)`, `Γ^{Q*}(Q₂) = g₂(b) + b (F₁ − F₂)`, and
`Λ^{Q*}(2, Q) = 2b (G₁ − G₂) + b (g₁(a) − g₂(b)) − (ρλ + ρ'(1−λ)) g₂(b) − (b² + ab)(F₁ − F₂)`. -/
theorem display_4_5 (lam ρ ρ' : ℝ) (hlam : 0 < lam ∧ lam < 1) (hρ : 0 ≤ ρ) (hρ' : 0 ≤ ρ')
    (g₁ g₂ : ℝ → ℝ) (a b as bs : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (has : 0 ≤ as) (hbs : 0 ≤ bs) :
    StrongWeakEq.Existence.Gamma (twoStatePayoff lam ρ ρ' g₁ g₂) (gen as bs) 0 (gen a b 0)
      = g₁ a - a * (StrongWeakEq.Existence.payoff (twoStatePayoff lam ρ ρ' g₁ g₂) (gen as bs) 0
                      - StrongWeakEq.Existence.payoff (twoStatePayoff lam ρ ρ' g₁ g₂) (gen as bs) 1) ∧
    StrongWeakEq.Existence.Gamma (twoStatePayoff lam ρ ρ' g₁ g₂) (gen as bs) 1 (gen a b 1)
      = g₂ b + b * (StrongWeakEq.Existence.payoff (twoStatePayoff lam ρ ρ' g₁ g₂) (gen as bs) 0
                      - StrongWeakEq.Existence.payoff (twoStatePayoff lam ρ ρ' g₁ g₂) (gen as bs) 1) ∧
    StrongWeakEq.Existence.Lambda (twoStatePayoff lam ρ ρ' g₁ g₂) (twoStatePayoffDeriv lam ρ ρ' g₁ g₂) (gen as bs) 1
        (gen a b)
      = 2 * b * (StrongWeakEq.Existence.payoffDeriv (twoStatePayoffDeriv lam ρ ρ' g₁ g₂) (gen as bs) 0
                  - StrongWeakEq.Existence.payoffDeriv (twoStatePayoffDeriv lam ρ ρ' g₁ g₂) (gen as bs) 1)
        + b * (g₁ a - g₂ b) - (ρ * lam + ρ' * (1 - lam)) * g₂ b
        - (b ^ 2 + a * b) * (StrongWeakEq.Existence.payoff (twoStatePayoff lam ρ ρ' g₁ g₂) (gen as bs) 0
                              - StrongWeakEq.Existence.payoff (twoStatePayoff lam ρ ρ' g₁ g₂) (gen as bs) 1) := by sorry

end StrongWeakEq.TwoState
