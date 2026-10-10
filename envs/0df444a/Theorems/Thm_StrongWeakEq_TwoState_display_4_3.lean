-- Prove2me | Theorems.Thm_StrongWeakEq_TwoState_display_4_3
-- name    : StrongWeakEq.TwoState.display_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T23:32:45.996325+00:00
-- url     : https://prove2.me/theorems/ae8152d5-0ee0-446d-b918-55fb2bcb9666
-- title:
--   (4.3)–(4.4), p. 12 — F₁ − F₂ and G₁ − G₂ in closed form for Q ∼ (a, b) under pseudo-exponential discounting
-- statement:
--   In the two-state model of §4 with pseudo-exponential discount $\delta(t)=\lambda e^{-\rho t}+(1-\lambda)e^{-\rho't}$, $\lambda\in(0,1)$, $\rho,\rho'>0$, and arbitrary $g_1,g_2$, write $F_i(a,b)=F(i,Q)$ and $G_i(a,b)=G(i,Q)$ for $Q\sim(a,b)$, $a,b\ge0$, where $G$ is computed with $f_t=\delta'(t)g$. Then
--   $$
--   F_1(a,b)-F_2(a,b)=\Big(\frac{\lambda}{\rho+a+b}+\frac{1-\lambda}{\rho'+a+b}\Big)\big(g_1(a)-g_2(b)\big), \tag{4.3}
--   $$
--   $$
--   G_1(a,b)-G_2(a,b)=-\Big(\frac{\rho\lambda}{\rho+a+b}+\frac{\rho'(1-\lambda)}{\rho'+a+b}\Big)\big(g_1(a)-g_2(b)\big). \tag{4.4}
--   $$
--
--   These closed forms turn $\Gamma$ and $\Lambda$ of the two-state model into explicit functions of $(a,b)$ and $(a^*,b^*)$, which is how Example 4.3 is computed.
--
--   **Formalization Note** The page allows $\rho,\rho'\ge0$ in (4.2), but with $\rho=0$ or $\rho'=0$ the payoff integral diverges ((3.8) fails) and the Lean Bochner integral would return the junk value $0$; the strict positivity $\rho,\rho'>0$ is therefore added. The page's intermediate quantities $\alpha=b/(a+b)$, $\beta=a/(a+b)$ are undefined at $a=b=0$; the formulas are stated directly and hold there too. State 1 is `0 : Fin 2`, state 2 is `1 : Fin 2`.
-- source:
--   Huang & Zhou, Strong and Weak Equilibria for Time-Inconsistent Stochastic Control in Continuous Time, arXiv:1809.09243v3, p. 12, (4.3), (4.4)

import Mathlib
import Definitions.Def_StrongWeakEq_Existence_Model
import Definitions.Def_StrongWeakEq_Existence_SecondOrder
import Definitions.Def_StrongWeakEq_TwoState_TwoStateModel

namespace StrongWeakEq.TwoState

/-- (4.3)–(4.4), p. 12: for `Q ∼ (a, b)` in the two-state model with pseudo-exponential discounting,
`F₁ − F₂ = (λ/(ρ+a+b) + (1−λ)/(ρ'+a+b)) (g₁(a) − g₂(b))` and
`G₁ − G₂ = −(ρλ/(ρ+a+b) + ρ'(1−λ)/(ρ'+a+b)) (g₁(a) − g₂(b))`. -/
theorem display_4_3 (lam ρ ρ' : ℝ) (hlam : 0 < lam ∧ lam < 1) (hρ : 0 < ρ) (hρ' : 0 < ρ')
    (g₁ g₂ : ℝ → ℝ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    StrongWeakEq.Existence.payoff (twoStatePayoff lam ρ ρ' g₁ g₂) (gen a b) 0
        - StrongWeakEq.Existence.payoff (twoStatePayoff lam ρ ρ' g₁ g₂) (gen a b) 1
      = (lam / (ρ + a + b) + (1 - lam) / (ρ' + a + b)) * (g₁ a - g₂ b) ∧
    StrongWeakEq.Existence.payoffDeriv (twoStatePayoffDeriv lam ρ ρ' g₁ g₂) (gen a b) 0
        - StrongWeakEq.Existence.payoffDeriv (twoStatePayoffDeriv lam ρ ρ' g₁ g₂) (gen a b) 1
      = -(ρ * lam / (ρ + a + b) + ρ' * (1 - lam) / (ρ' + a + b)) * (g₁ a - g₂ b) := by sorry

end StrongWeakEq.TwoState
