-- Prove2me | Theorems.Thm_RUCVaR_MinFormula_theorem_10
-- name    : RUCVaR.MinFormula.theorem_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:05:24.972272+00:00
-- url     : https://prove2.me/theorems/b769eeb9-75d6-4d3c-a27f-3baf0310effe
-- title:
--   Theorem 10, p. 14 — φ_β(x) = min_α F_β(x, α), argmin = [α_β(x), α⁺_β(x)], F_β(x, ·) finite convex
-- statement:
--   **Theorem 10 (fundamental minimization formula).** Let $P$ be a Borel probability measure on $\mathbb R^m$, the law of the random vector $y$, and let $f(x,y)$ be the loss of a decision $x\in X\subseteq\mathbb R^n$, continuous in $x$ on $X$, measurable in $y$, with $E\{|f(x,y)|\}<\infty$ for each $x\in X$. Let $0<\beta<1$ and $x\in X$. Write
--   $$
--   F_\beta(x,\alpha)=\alpha+\frac{1}{1-\beta}E\big\{[f(x,y)-\alpha]^+\big\},
--   $$
--   $\alpha_\beta(x)$ for the β-VaR, $\alpha_\beta^+(x)$ for the upper β-VaR, and $\phi_\beta(x)$ for the β-CVaR, the mean of the β-tail distribution. Then:
--
--   1. $F_\beta(x,\alpha)$ is finite for every $\alpha$, and $F_\beta(x,\cdot)$ is convex, hence continuous;
--   2. the minimum of $F_\beta(x,\cdot)$ is attained and equals the β-CVaR:
--   $$
--   \phi_\beta(x)=\min_\alpha F_\beta(x,\alpha); \tag{28}
--   $$
--   3. $\alpha_\beta(x)\le\alpha^+_\beta(x)$, and the argmin is the nonempty closed bounded interval
--   $$
--   \operatorname{argmin}_\alpha F_\beta(x,\alpha)=[\alpha_\beta(x),\alpha^+_\beta(x)]; \tag{29}
--   $$
--   4. in particular $\alpha_\beta(x)\in\operatorname{argmin}_\alpha F_\beta(x,\alpha)$ and $\phi_\beta(x)=F_\beta(x,\alpha_\beta(x))$. (30)
--
--   VaR and CVaR of the loss are thus computed together by minimizing a convex function of one real variable, for any loss distribution, discrete or continuous.
--
--   **Formalization Note** "Finite" is integrability of $[f(x,\cdot)-\alpha]^+$ for every $\alpha$. "min with attainment" is stated as: $\phi_\beta(x)$ is the least element of the range of $F_\beta(x,\cdot)$. The argmin is the set of global minimizers. $\phi_\beta(x)$ is defined as the mean of the β-tail distribution of Definition 3, not through $F_\beta$, so (28) is not true by definition. All standing assumptions of §2 are carried even though only integrability of the loss at the given $x$ is used.
-- source:
--   Rockafellar & Uryasev, Conditional value-at-risk for general loss distributions, Research Report #2001-5, Univ. of Florida, April 4, 2001, p. 14, Theorem 10, (27)–(30)

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_RUCVaR_MinFormula_Setting
open MeasureTheory Filter Topology

namespace RUCVaR.MinFormula

/-- Theorem 10 (fundamental minimization formula), p. 14, (28)–(30). -/
theorem theorem_10 {m n : ℕ} (P : Measure (Fin m → ℝ)) [IsProbabilityMeasure P]
    (X : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (hf_cont : ∀ y, ContinuousOn (fun x => f x y) X) (hf_meas : ∀ x, Measurable (f x))
    (hf_int : ∀ x ∈ X, Integrable (f x) P) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (x : Fin n → ℝ) (hx : x ∈ X) :
    (∀ α : ℝ, Integrable (fun y => max (f x y - α) 0) P) ∧
    ConvexOn ℝ Set.univ (Fbeta P f β x) ∧ Continuous (Fbeta P f β x) ∧
    IsLeast (Set.range (Fbeta P f β x)) (CVaR P f β x) ∧
    (VaR P f β x ≤ VaRPlus P f β x ∧
      {α : ℝ | IsMinOn (Fbeta P f β x) Set.univ α} = Set.Icc (VaR P f β x) (VaRPlus P f β x)) ∧
    (IsMinOn (Fbeta P f β x) Set.univ (VaR P f β x) ∧
      CVaR P f β x = Fbeta P f β x (VaR P f β x)) := by sorry

end RUCVaR.MinFormula
