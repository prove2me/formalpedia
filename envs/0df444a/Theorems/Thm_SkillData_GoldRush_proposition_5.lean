-- Prove2me | Theorems.Thm_SkillData_GoldRush_proposition_5
-- name    : SkillData.GoldRush.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:22:58.571791+00:00
-- url     : https://prove2.me/theorems/dde3107c-daaf-4ca1-8c15-9836cbe95528
-- title:
--   Proposition 5, pp. 21–22 (PDF 22–23) — with ZL < ZH and high τη, a higher cost lowers λ∗, E(θ̃−p̃), σ(θ̃−p̃) and raises x∗, q∗, 1/Var(θ̃|p̃), Performance
-- statement:
--   Assume the standing assumptions, so that skill acquisition is uncertain ($\Delta>0$, i.e. $Z_L<Z_H$), and let $C$ be an admissible cost family. Fix two cost parameters $0<c_1<c_2$. Then there is a threshold $T$ with the following property. Take any data accuracy $\tau_\eta\ge T$, any equilibrium $(x_1^*,\lambda_1^*,\alpha_1^*)$ at cost $c_1$ and any equilibrium $(x_2^*,\lambda_2^*,\alpha_2^*)$ at cost $c_2$. Then both clarities are finite, $x_1^*,x_2^*<\infty$, and:
--
--   1. the population of skilled investors decreases: $\lambda_2^*<\lambda_1^*$;
--   2. data clarity increases: $x_1^*<x_2^*$;
--   3. the data price increases: $q_1^*<q_2^*$, where $q^*=\beta G(x^*,\alpha^*)$;
--   4. price informativeness increases: $\dfrac{1}{\operatorname{Var}(\tilde\theta\mid\tilde p)}\Big|_{1}<\dfrac{1}{\operatorname{Var}(\tilde\theta\mid\tilde p)}\Big|_{2}$;
--   5. the cost of capital decreases: $E(\tilde\theta-\tilde p)_2<E(\tilde\theta-\tilde p)_1$;
--   6. return volatility decreases: $\sigma(\tilde\theta-\tilde p)_2<\sigma(\tilde\theta-\tilde p)_1$;
--   7. skilled investors' performance increases: $\mathrm{Performance}_1<\mathrm{Performance}_2$.
--
--   In the paper's notation, for sufficiently high $\tau_\eta$,
--   $$\frac{\partial\lambda^*}{\partial c}<0,\quad \frac{\partial x^*}{\partial c}>0,\quad \frac{\partial q^*}{\partial c}>0,\quad \frac{\partial}{\partial c}\frac{1}{\operatorname{Var}(\tilde\theta\mid\tilde p)}>0,\quad \frac{\partial E(\tilde\theta-\tilde p)}{\partial c}<0,\quad \frac{\partial\sigma(\tilde\theta-\tilde p)}{\partial c}<0,\quad \frac{\partial\,\mathrm{Performance}}{\partial c}>0.$$
--
--   This is the paper's headline result: when skill acquisition is uncertain, price informativeness *increases* with skill-acquisition costs. Without skill uncertainty, price informativeness stays unchanged (Proposition 4).
--
--   **Formalization Note.** The derivatives in $c$ are read as strict comparisons between two cost levels $c_1<c_2$, as in the proposition's prose. The paper does not establish that the equilibrium quantities are differentiable in $c$, or that the equilibrium is unique. "For sufficiently high $\tau_\eta$" is $\exists T\,\forall\tau_\eta\ge T$, and the threshold may depend on $c_1,c_2$. The comparisons hold for every pair of equilibria. That both clarities are finite is part of the conclusion, not a hypothesis. The cost family is any admissible one, not the illustrative $ci/(1-i)$ of the figures. The standing assumptions add $\beta>0$ and $Z_L>0$ to the page's parameter domains.
-- source:
--   Huang, Xiong & Yang, Skill Acquisition and Data Sales, working paper (July 2019 version), pp. 21–22 (PDF 22–23), Proposition 5

import Mathlib
import Definitions.Def_SkillData_GoldRush_Model

namespace SkillData.GoldRush

theorem proposition_5 (P : Params) (hP : P.Standing) (C : ℝ → ℝ → ℝ) (hC : IsCostFamily C)
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc : c₁ < c₂) :
    ∃ T : ℝ, ∀ τη : ℝ, T ≤ τη →
      ∀ (X₁ : Clarity) (lam₁ α₁ : ℝ) (X₂ : Clarity) (lam₂ α₂ : ℝ),
        IsEquilibrium P C c₁ τη X₁ lam₁ α₁ → IsEquilibrium P C c₂ τη X₂ lam₂ α₂ →
        ∃ x₁ x₂ : ℝ, X₁ = .finite x₁ ∧ X₂ = .finite x₂ ∧
          lam₂ < lam₁ ∧ x₁ < x₂ ∧
          dataPrice P τη x₁ α₁ < dataPrice P τη x₂ α₂ ∧
          priceInformativeness P τη α₁ < priceInformativeness P τη α₂ ∧
          costOfCapital P τη x₂ lam₂ α₂ < costOfCapital P τη x₁ lam₁ α₁ ∧
          returnVolatility P τη x₂ lam₂ α₂ < returnVolatility P τη x₁ lam₁ α₁ ∧
          performance P τη x₁ α₁ < performance P τη x₂ α₂ := by sorry

end SkillData.GoldRush
