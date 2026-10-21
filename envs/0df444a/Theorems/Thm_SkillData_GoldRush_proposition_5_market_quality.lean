-- Prove2me | Theorems.Thm_SkillData_GoldRush_proposition_5_market_quality
-- name    : SkillData.GoldRush.proposition_5_market_quality
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-21T02:28:59.735538+00:00
-- url     : https://prove2.me/theorems/9f81869a-8177-4a03-b462-42ffc219f061
-- title:
--   Proposition 5 (market quality), pp. 21–22 — for high τη a higher cost raises 1/Var(θ̃|p̃) and lowers E(θ̃−p̃), σ(θ̃−p̃)
-- statement:
--   Assume the standing assumptions, so that skill acquisition is uncertain ($Z_L<Z_H$), and let $C$ be an admissible cost family. Fix two cost parameters $0<c_1<c_2$. Then there is a threshold $T$ with the following property. Take any data accuracy $\tau_\eta\ge T$, any equilibrium $(x_1^*,\lambda_1^*,\alpha_1^*)$ at cost $c_1$ and any equilibrium $(x_2^*,\lambda_2^*,\alpha_2^*)$ at cost $c_2$, both with finite clarity. Then:
--
--   1. price informativeness increases: $\dfrac{1}{\operatorname{Var}(\tilde\theta\mid\tilde p)}\Big|_{1}<\dfrac{1}{\operatorname{Var}(\tilde\theta\mid\tilde p)}\Big|_{2}$, i.e. $\alpha_1^*<\alpha_2^*$;
--   2. the cost of capital decreases: $E(\tilde\theta-\tilde p)_2<E(\tilde\theta-\tilde p)_1$, where $E(\tilde\theta-\tilde p)=-a_0$ is (C12);
--   3. return volatility decreases: $\sigma(\tilde\theta-\tilde p)_2<\sigma(\tilde\theta-\tilde p)_1$, where $\sigma$ is (C13).
--
--   In the paper's notation, for sufficiently high $\tau_\eta$,
--   $$\frac{\partial}{\partial c}\frac{1}{\operatorname{Var}(\tilde\theta\mid\tilde p)}>0,\qquad \frac{\partial E(\tilde\theta-\tilde p)}{\partial c}<0,\qquad \frac{\partial\sigma(\tilde\theta-\tilde p)}{\partial c}<0.$$
--
--   These are the market-quality claims of Proposition 5. They are second-order effects in $w=1/\tau_\eta$: at $w=0$ the limits of all three quantities do not depend on $c$ (pp. 39–40). In the paper's proof the sign comes from the first-order term of $\alpha(\lambda;w)$ in (C17), together with $\partial\lambda^*/\partial c<0$.
--
--   **Formalization Note.** This is the market-quality part of the goal `SkillData.GoldRush.proposition_5`, with the same reading: derivatives in $c$ are strict comparisons between $c_1<c_2$, "sufficiently high $\tau_\eta$" is $\exists T\,\forall\tau_\eta\ge T$, and the comparisons hold for every pair of equilibria. Finiteness of both clarities is a hypothesis here. The goal's remaining claims ($\lambda$, $x$, $q$, performance, finiteness) are proved separately in the reduction of the goal to this statement.
-- source:
--   Huang, Xiong & Yang, Skill Acquisition and Data Sales, working paper (July 2019 version), pp. 21–22 (PDF 22–23), Proposition 5; proof pp. 38–40 (PDF 39–41), (C14)–(C17) and the market-quality paragraph

import Mathlib
import Definitions.Def_SkillData_GoldRush_Model

namespace SkillData.GoldRush

theorem proposition_5_market_quality (P : Params) (hP : P.Standing) (C : ℝ → ℝ → ℝ)
    (hC : IsCostFamily C) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc : c₁ < c₂) :
    ∃ T : ℝ, ∀ τη : ℝ, T ≤ τη →
      ∀ (X₁ : Clarity) (lam₁ α₁ : ℝ) (X₂ : Clarity) (lam₂ α₂ : ℝ),
        IsEquilibrium P C c₁ τη X₁ lam₁ α₁ → IsEquilibrium P C c₂ τη X₂ lam₂ α₂ →
        ∀ x₁ x₂ : ℝ, X₁ = .finite x₁ → X₂ = .finite x₂ →
          priceInformativeness P τη α₁ < priceInformativeness P τη α₂ ∧
          costOfCapital P τη x₂ lam₂ α₂ < costOfCapital P τη x₁ lam₁ α₁ ∧
          returnVolatility P τη x₂ lam₂ α₂ < returnVolatility P τη x₁ lam₁ α₁ := by sorry

end SkillData.GoldRush
