-- Prove2me | Theorems.Thm_RUCVaR_MinFormula_proposition_6
-- name    : RUCVaR.MinFormula.proposition_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:05:07.063298+00:00
-- url     : https://prove2.me/theorems/122beac7-f012-4791-999d-29c90ebe274f
-- title:
--   Proposition 6, p. 10 — φ_β(x) = λ_β(x)α_β(x) + [1 − λ_β(x)]φ⁺_β(x) if Ψ(x, α_β(x)) < 1, φ_β(x) = α_β(x) otherwise
-- statement:
--   Let $P$ be a probability measure on $\mathbb R^m$, let the loss $y\mapsto f(x,y)$ be measurable and integrable, and let $0<\beta<1$. Write $\alpha_\beta(x)$ for the β-VaR, $\phi_\beta(x)$ for the β-CVaR (the mean of the β-tail distribution), $\phi^+_\beta(x)=E\{f(x,y)\mid f(x,y)>\alpha_\beta(x)\}$ for the upper β-CVaR, and
--   $$
--   \lambda_\beta(x)=\frac{\Psi(x,\alpha_\beta(x))-\beta}{1-\beta}.
--   $$
--   Then:
--
--   1. $0\le\lambda_\beta(x)\le1$;
--   2. if $\Psi(x,\alpha_\beta(x))<1$, then $\lambda_\beta(x)<1$ and
--   $$
--   \phi_\beta(x)=\lambda_\beta(x)\,\alpha_\beta(x)+[1-\lambda_\beta(x)]\,\phi^+_\beta(x);
--   $$
--   3. if $\Psi(x,\alpha_\beta(x))=1$, then $\lambda_\beta(x)=1$ and $\phi_\beta(x)=\alpha_\beta(x)$.
--
--   The proposition expresses CVaR as a weighted average of VaR and the upper CVaR, the weight being the part of the probability atom at the VaR that the β-tail distribution keeps. It is the bridge from the definition of CVaR as a tail mean to the formula $F_\beta(x,\alpha_\beta(x))$ of Theorem 10.
--
--   **Formalization Note** The upper CVaR is an elementary conditional expectation, a quotient by $P\{f(x,\cdot)>\alpha_\beta(x)\}$, and it is used only under $\Psi(x,\alpha_\beta(x))<1$, where that probability is positive. The paper's standing assumptions are reduced to the single loss $f(x,\cdot)$ (measurable and integrable), which makes the statement stronger.
-- source:
--   Rockafellar & Uryasev, Conditional value-at-risk for general loss distributions, Research Report #2001-5, Univ. of Florida, April 4, 2001, p. 10, Proposition 6, (20)–(22)

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_RUCVaR_MinFormula_Setting
open MeasureTheory Filter Topology

namespace RUCVaR.MinFormula

/-- Proposition 6 (CVaR as a weighted average), p. 10, (20)–(22). -/
theorem proposition_6 {m n : ℕ} (P : Measure (Fin m → ℝ)) [IsProbabilityMeasure P]
    (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (x : Fin n → ℝ) (hmeas : Measurable (f x))
    (hint : Integrable (f x) P) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    (0 ≤ lambdaBeta P f β x ∧ lambdaBeta P f β x ≤ 1) ∧
    (Psi P f x (VaR P f β x) < 1 →
      lambdaBeta P f β x < 1 ∧
      CVaR P f β x = lambdaBeta P f β x * VaR P f β x
        + (1 - lambdaBeta P f β x) * CVaRPlus P f β x) ∧
    (Psi P f x (VaR P f β x) = 1 →
      lambdaBeta P f β x = 1 ∧ CVaR P f β x = VaR P f β x) := by sorry

end RUCVaR.MinFormula
