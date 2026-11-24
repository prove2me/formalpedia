-- Prove2me | Theorems.Thm_RUCVaR_MinFormula_Supplement_theorem_14
-- name    : RUCVaR.MinFormula.Supplement.theorem_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T05:15:10.404541+00:00
-- url     : https://prove2.me/theorems/85e705a9-2311-40e1-8771-b764e2f10d22
-- title:
--   Theorem 14, p. 19 — optimization shortcut: minimizing φ_β over X is minimizing F_β(x, α) jointly over X × ℝ
-- statement:
--   Let $P$ be a Borel probability measure on $\mathbb R^m$, the law of a random vector $y$, let $X\subseteq\mathbb R^n$ be a set of decisions, and let $f(x,y)$ be the loss of decision $x$ under outcome $y$. Assume that $f(x,y)$ is continuous in $x$ on $X$ for every $y$, measurable in $y$ for every $x$, and that $E\{|f(x,y)|\}<\infty$ for every $x\in X$. Fix a confidence level $\beta\in(0,1)$. Write $\phi_\beta(x)$ for the $\beta$-CVaR of the loss $f(x,y)$, the mean of its $\beta$-tail distribution (Definition 3), and
--   $$
--   F_\beta(x,\alpha)=\alpha+\frac{1}{1-\beta}\,E\big\{[f(x,y)-\alpha]^+\big\}.
--   $$
--
--   **Theorem 14 (optimization shortcut).** Minimizing $\phi_\beta(x)$ over $x\in X$ is equivalent to minimizing $F_\beta(x,\alpha)$ over all $(x,\alpha)\in X\times\mathbb R$:
--
--   1. the two optimal values coincide,
--   $$
--   \inf_{x\in X}\phi_\beta(x)=\inf_{(x,\alpha)\in X\times\mathbb R}F_\beta(x,\alpha),
--   $$
--   2. and for every $x^*\in\mathbb R^n$ and $\alpha^*\in\mathbb R$,
--   $$
--   (x^*,\alpha^*)\in\operatorname*{argmin}_{(x,\alpha)\in X\times\mathbb R}F_\beta(x,\alpha)
--   \iff x^*\in\operatorname*{argmin}_{x\in X}\phi_\beta(x)\ \text{ and }\ \alpha^*\in\operatorname*{argmin}_{\alpha\in\mathbb R}F_\beta(x^*,\alpha).
--   $$
--
--   The theorem turns the minimization of CVaR, whose definition involves a quantile, into the minimization of an expectation in the enlarged variable $(x,\alpha)$; an optimal $\alpha^*$ is then a minimizer of $F_\beta(x^*,\cdot)$, which by Theorem 10 lies in $[\alpha_\beta(x^*),\alpha^+_\beta(x^*)]$.
--
--   **Formalization Note** The infima in (1) are taken in the extended reals $[-\infty,+\infty]$, so they are meaningful when they are not attained, when they are $-\infty$, and when $X$ is empty (both sides are then $+\infty$). Membership in an argmin is global minimality on the stated set; the argmin over $X\times\mathbb R$ contains only points with $x^*\in X$.
--
--   Differences from the source:
--   - reading: (43) is written with "min" on both sides, but $X$ is an arbitrary set and attainment is not assumed → equality of the infima in the extended reals; reason: the paper proves the identity of optimal values whether or not they are attained, and attainment on one side is equivalent to attainment on the other by (44).
--   - encoding: $P$ a Borel probability measure on a set $Y\subseteq\mathbb R^m$ → $P$ a Borel probability measure on $\mathbb R^m$; reason: a law on $Y$ is a law on $\mathbb R^m$ concentrated on $Y$, and the statement does not use $Y$.
-- source:
--   Rockafellar & Uryasev, Conditional value-at-risk for general loss distributions, Research Report #2001-5, Univ. of Florida, April 4, 2001, p. 19, Theorem 14, (43)–(44); standing setting p. 5

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_RUCVaR_MinFormula_Setting
open MeasureTheory

namespace RUCVaR.MinFormula.Supplement

/-- Theorem 14 (optimization shortcut), p. 19, (43)–(44). The minimum over `X` in (43) is not
assumed attained, so (43) is the equality of the two infima, taken in `EReal`. -/
theorem theorem_14 {m n : ℕ} (P : Measure (Fin m → ℝ)) [IsProbabilityMeasure P]
    (X : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (hf_cont : ∀ y, ContinuousOn (fun x => f x y) X) (hf_meas : ∀ x, Measurable (f x))
    (hf_int : ∀ x ∈ X, Integrable (f x) P) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ((⨅ x ∈ X, (RUCVaR.MinFormula.CVaR P f β x : EReal)) =
      ⨅ x ∈ X, ⨅ α : ℝ, (RUCVaR.MinFormula.Fbeta P f β x α : EReal)) ∧
    ∀ (xs : Fin n → ℝ) (αs : ℝ),
      ((xs ∈ X ∧ IsMinOn (fun p : (Fin n → ℝ) × ℝ => RUCVaR.MinFormula.Fbeta P f β p.1 p.2)
          (X ×ˢ Set.univ) (xs, αs)) ↔
        (xs ∈ X ∧ IsMinOn (RUCVaR.MinFormula.CVaR P f β) X xs ∧
          IsMinOn (RUCVaR.MinFormula.Fbeta P f β xs) Set.univ αs)) := by sorry

end RUCVaR.MinFormula.Supplement
