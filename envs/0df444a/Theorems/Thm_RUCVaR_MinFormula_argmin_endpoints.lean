-- Prove2me | Theorems.Thm_RUCVaR_MinFormula_argmin_endpoints
-- name    : RUCVaR.MinFormula.argmin_endpoints
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:04:59.27598+00:00
-- url     : https://prove2.me/theorems/81f726f2-4ba1-4a7b-894a-d082476626bc
-- title:
--   Proof of Theorem 10, p. 16 — the lowest α with Ψ(x, α⁻) ≤ β ≤ Ψ(x, α) is α_β(x), the highest is α⁺_β(x)
-- statement:
--   Let $P$ be a probability measure on $\mathbb R^m$, let the loss $y\mapsto f(x,y)$ be measurable, and let $0<\beta<1$. Consider
--   $$
--   S=\{\alpha\in\mathbb R \mid \Psi(x,\alpha^-)\le\beta\le\Psi(x,\alpha)\}.
--   $$
--   Then the β-VaR $\alpha_\beta(x)=\min\{\alpha\mid\Psi(x,\alpha)\ge\beta\}$ is the least element of $S$, and the upper β-VaR $\alpha^+_\beta(x)=\inf\{\alpha\mid\Psi(x,\alpha)>\beta\}$ is the greatest element of $S$.
--
--   Combined with the characterization of the argmin of $F_\beta(x,\cdot)$ as $S$, this gives (29): the argmin is the interval $[\alpha_\beta(x),\alpha^+_\beta(x)]$.
--
--   **Formalization Note** No integrability is needed: the claim is about the distribution function of the loss only. Both endpoints are real infima, which are meaningful because $P$ is a probability measure and $0<\beta<1$; those hypotheses are kept.
-- source:
--   Rockafellar & Uryasev, Conditional value-at-risk for general loss distributions, Research Report #2001-5, Univ. of Florida, April 4, 2001, p. 16, proof of Theorem 10, Definitions 1–2, (4), (6), (29)

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_RUCVaR_MinFormula_Setting
open MeasureTheory Filter Topology

namespace RUCVaR.MinFormula

/-- Proof of Theorem 10, p. 16: the lowest `α` with `Ψ(x, α⁻) ≤ β ≤ Ψ(x, α)` is `α_β(x)`
(Definition 1) and the highest is `α⁺_β(x)` (Definition 2). -/
theorem argmin_endpoints {m n : ℕ} (P : Measure (Fin m → ℝ)) [IsProbabilityMeasure P]
    (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (x : Fin n → ℝ) (hmeas : Measurable (f x))
    (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    IsLeast {α : ℝ | PsiLeft P f x α ≤ β ∧ β ≤ Psi P f x α} (VaR P f β x) ∧
    IsGreatest {α : ℝ | PsiLeft P f x α ≤ β ∧ β ≤ Psi P f x α} (VaRPlus P f β x) := by sorry

end RUCVaR.MinFormula
