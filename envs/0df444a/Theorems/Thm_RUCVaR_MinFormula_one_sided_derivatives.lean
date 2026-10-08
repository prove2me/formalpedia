-- Prove2me | Theorems.Thm_RUCVaR_MinFormula_one_sided_derivatives
-- name    : RUCVaR.MinFormula.one_sided_derivatives
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:04:55.291104+00:00
-- url     : https://prove2.me/theorems/14cb18f1-4813-4214-9e29-24f4a0675e3f
-- title:
--   (31), proof of Theorem 10, p. 15 — ∂⁺F_β/∂α = [Ψ(x, α) − β]/(1 − β), ∂⁻F_β/∂α = [Ψ(x, α⁻) − β]/(1 − β)
-- statement:
--   Let $P$ be a probability measure on $\mathbb R^m$, let the loss $y\mapsto f(x,y)$ be measurable and integrable, and let $\beta<1$. Then at every $\alpha\in\mathbb R$ the function $F_\beta(x,\cdot)$ of (27) has one-sided derivatives
--   $$
--   \frac{\partial^+F_\beta}{\partial\alpha}(x,\alpha)=\frac{\Psi(x,\alpha)-\beta}{1-\beta},\qquad
--   \frac{\partial^-F_\beta}{\partial\alpha}(x,\alpha)=\frac{\Psi(x,\alpha^-)-\beta}{1-\beta},
--   $$
--   where $\Psi(x,\alpha)=P\{f(x,y)\le\alpha\}$ and $\Psi(x,\alpha^-)=P\{f(x,y)<\alpha\}$.
--
--   These formulas reduce the minimization of the convex function $F_\beta(x,\cdot)$ to the optimality condition $\Psi(x,\alpha^-)\le\beta\le\Psi(x,\alpha)$.
--
--   **Formalization Note** The right derivative is a derivative within $[\alpha,\infty)$ and the left derivative one within $(-\infty,\alpha]$. The display (31) printed on p. 14 has $\alpha_\beta(x)$ where the general $\alpha$ belongs ($\Psi(x,\alpha_\beta(x))$ and $\Psi(x,\alpha_\beta(x)^-)$); taken literally it is false wherever $\Psi(x,\cdot)$ changes value. The statement follows the derivation on p. 15 and the use on p. 16, which have $\Psi(x,\alpha)$ and $\Psi(x,\alpha^-)$. The bound $\beta>0$ and the other standing assumptions are not needed and are dropped.
-- source:
--   Rockafellar & Uryasev, Conditional value-at-risk for general loss distributions, Research Report #2001-5, Univ. of Florida, April 4, 2001, pp. 14–15, proof of Theorem 10, (31)–(32)

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_RUCVaR_MinFormula_Setting
open MeasureTheory Filter Topology

namespace RUCVaR.MinFormula

/-- (31), proof of Theorem 10, pp. 14–15, in the form derived on p. 15: the right derivative of
`F_β(x, ·)` at `α` is `[Ψ(x, α) − β]/(1 − β)` and the left derivative is
`[Ψ(x, α⁻) − β]/(1 − β)`. (The p. 14 display prints `α_β(x)` in place of `α`; see the
moderation notes.) -/
theorem one_sided_derivatives {m n : ℕ} (P : Measure (Fin m → ℝ)) [IsProbabilityMeasure P]
    (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (x : Fin n → ℝ) (hmeas : Measurable (f x))
    (hint : Integrable (f x) P) (β : ℝ) (hβ1 : β < 1) (α : ℝ) :
    HasDerivWithinAt (Fbeta P f β x) ((Psi P f x α - β) / (1 - β)) (Set.Ici α) α ∧
    HasDerivWithinAt (Fbeta P f β x) ((PsiLeft P f x α - β) / (1 - β)) (Set.Iic α) α := by sorry

end RUCVaR.MinFormula
