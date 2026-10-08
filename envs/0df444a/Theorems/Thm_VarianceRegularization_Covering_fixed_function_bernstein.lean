-- Prove2me | Theorems.Thm_VarianceRegularization_Covering_fixed_function_bernstein
-- name    : VarianceRegularization.Covering.fixed_function_bernstein
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T19:41:00.414979+00:00
-- url     : https://prove2.me/theorems/ea2e1ee1-2d3c-42ec-beff-5744b43e3af9
-- title:
--   Appendix C, p. 38 — Bernstein's inequality for one fixed bounded function
-- statement:
--   Let $f : \mathcal X \to [M_0, M_1]$ be a fixed measurable function, $M = M_1 - M_0$, and let $X_1, \dots, X_n$ ($n \ge 1$) be i.i.d. with law $P$. Write $\mathbb E[f] = \int f\, dP$, $\mathrm{Var}(f)$ for the variance of $f(X)$ and $\mathbb E_{\widehat P_n}[f] = \frac1n \sum_i f(X_i)$. Then for every $t > 0$, with probability at least $1 - e^{-t}$,
--   $$
--   \mathbb E_{\widehat P_n}[f] \le \mathbb E[f] + \sqrt{\frac{2\,\mathrm{Var}(f)\, t}{n}} + \frac{2Mt}{3n}.
--   $$
--
--   This is the one-sided Bernstein inequality for bounded i.i.d. variables, in the form used in the proof of the oracle inequality (16) of Theorem 3 for the comparison function $f$.
--
--   **Formalization Note** The sample is the coordinate process of the product measure $P^{\otimes n}$; the statement bounds the probability of the event where the inequality fails by $e^{-t}$. Since $f$ is bounded and measurable, its mean and variance are the true values.
-- source:
--   Duchi and Namkoong, Variance-based regularization with convex objectives, arXiv:1610.02581v3 (2017), p. 38, Appendix C (proof of Theorem 3), display following "by Bernstein's inequality, we have"

import Mathlib
import Definitions.Def_VarianceRegularization_Covering_robustSup

open MeasureTheory ProbabilityTheory

namespace VarianceRegularization.Covering

/-- Appendix C, proof of Theorem 3, Bernstein display (Duchi–Namkoong, arXiv:1610.02581v3,
p. 38): for one fixed measurable `f : X → [M₀, M₁]`, `M = M₁ - M₀`, an i.i.d. sample
`X₁,…,Xₙ ~ P` and `t > 0`, with probability at least `1 - e^{-t}`,
`E_{P̂ₙ}[f] ≤ E[f] + √(2 Var(f) t / n) + 2Mt/(3n)`.
Stated as: the event where this fails has probability at most `e^{-t}`. -/
theorem fixed_function_bernstein {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (M0 M1 : ℝ) (hM : M0 ≤ M1) (f : X → ℝ) (hf : Measurable f)
    (hfb : ∀ x, f x ∈ Set.Icc M0 M1) (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 < t) :
    Measure.pi (fun _ : Fin n => P)
        {s | ∫ x, f x ∂P + Real.sqrt (2 * variance f P * t / n) + 2 * (M1 - M0) * t / (3 * n)
          < empMean f s}
      ≤ ENNReal.ofReal (Real.exp (-t)) := by sorry

end VarianceRegularization.Covering
