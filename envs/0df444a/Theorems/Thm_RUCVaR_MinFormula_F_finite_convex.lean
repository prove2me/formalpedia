-- Prove2me | Theorems.Thm_RUCVaR_MinFormula_F_finite_convex
-- name    : RUCVaR.MinFormula.F_finite_convex
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T00:05:08.674813+00:00
-- url     : https://prove2.me/theorems/53d3c14c-02fa-4d34-94dd-40ab19b3829c
-- title:
--   Proof of Theorem 10, p. 14 — F_β(x, ·) is finite and convex
-- statement:
--   Let $P$ be a probability measure on $\mathbb R^m$, let the loss $y\mapsto f(x,y)$ be integrable, and let $\beta<1$. Then for every $\alpha\in\mathbb R$ the positive part $[f(x,\cdot)-\alpha]^+$ is integrable, so
--   $$
--   F_\beta(x,\alpha)=\alpha+\frac{1}{1-\beta}E\big\{[f(x,y)-\alpha]^+\big\}
--   $$
--   is finite, and $\alpha\mapsto F_\beta(x,\alpha)$ is convex on $\mathbb R$.
--
--   These are the first two assertions of Theorem 10; they make the one-sided derivatives of $F_\beta(x,\cdot)$ available.
--
--   **Formalization Note** "Finite" is stated as integrability of $[f(x,\cdot)-\alpha]^+$ for every $\alpha$, since a real-valued Lean integral is $0$ for a non-integrable function. Only integrability of the single loss and $\beta<1$ are assumed; the remaining standing assumptions of §2 are not needed and are dropped, which makes the statement stronger.
-- source:
--   Rockafellar & Uryasev, Conditional value-at-risk for general loss distributions, Research Report #2001-5, Univ. of Florida, April 4, 2001, p. 14, proof of Theorem 10, (27)

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_RUCVaR_MinFormula_Setting
open MeasureTheory Filter Topology

namespace RUCVaR.MinFormula

/-- Proof of Theorem 10, p. 14: `F_β(x, ·)` is finite and convex. -/
theorem F_finite_convex {m n : ℕ} (P : Measure (Fin m → ℝ)) [IsProbabilityMeasure P]
    (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (x : Fin n → ℝ) (hint : Integrable (f x) P)
    (β : ℝ) (hβ1 : β < 1) :
    (∀ α : ℝ, Integrable (fun y => max (f x y - α) 0) P) ∧
    ConvexOn ℝ Set.univ (Fbeta P f β x) := by sorry

end RUCVaR.MinFormula
