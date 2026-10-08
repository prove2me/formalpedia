-- Prove2me | Theorems.Thm_StoneRegression_Quantile_proposition_14
-- name    : StoneRegression.Quantile.proposition_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:22:35.241421+00:00
-- url     : https://prove2.me/theorems/d117fe47-37e1-4f7c-956c-ade7a7fb27d2
-- title:
--   Proposition 14, p. 616 — E|L(p|X)|ʳ and E|U(p|X)|ʳ are at most E|Y|ʳ/(p ∧ (1 − p))
-- statement:
--   Let $0<p<1$ and $r\ge1$, let $X$ have law $\mu$ on $\mathbb R^d$ and let $Y$ be real with conditional law $\kappa$ given $X$. Then the lower and upper $p$th conditional quantiles satisfy
--   $$E|L^Y(p\mid X)|^r\le\frac{E|Y|^r}{p\wedge(1-p)}\qquad\text{and}\qquad E|U^Y(p\mid X)|^r\le\frac{E|Y|^r}{p\wedge(1-p)},$$
--   where $p\wedge(1-p)=\min(p,1-p)$.
--
--   The bound shows that the conditional quantiles inherit the $r$th moment of $Y$. It is the integrability input for the $L^r$ part of Theorem 3.
--
--   **Formalization Note.** The page states the proposition for $r>1$; the proof of Theorem 3 applies it for every $r\ge1$, and the page's argument does not use $r>1$. The Lean statement takes $r\ge1$, the range the paper uses. Expectations are $[0,\infty]$-valued lower integrals, so the inequality is meaningful (and true) also when $E|Y|^r=\infty$.
-- source:
--   Stone (1977), Ann. Statist. 5, Proposition 14, p. 616 (§12); printed hypothesis r > 1 widened to r ≥ 1 as used in the proof of Theorem 3, p. 617

import Mathlib
import Definitions.Def_StoneRegression_Criterion_Setting
import Definitions.Def_StoneRegression_Quantile_Quantiles

namespace StoneRegression.Quantile

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

/-- Proposition 14, p. 616 (range of `r` corrected from the printed `r > 1` to `r ≥ 1`, the range the
proof of Theorem 3 uses): `E|L(p|X)|ʳ ≤ E|Y|ʳ / (p ∧ (1 − p))` and the same for `U(p|X)`, with all
expectations as `ℝ≥0∞`-valued lower integrals (both sides may be `∞`). -/
theorem proposition_14 {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (κ : Kernel (EuclideanSpace ℝ (Fin d)) ℝ) [IsMarkovKernel κ]
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (r : ℝ) (hr : 1 ≤ r) :
    ∫⁻ x, ‖lowerQ κ p x‖ₑ ^ r ∂μ ≤
        (∫⁻ q, ‖q.2‖ₑ ^ r ∂(μ ⊗ₘ κ)) / ENNReal.ofReal (min p (1 - p)) ∧
    ∫⁻ x, ‖upperQ κ p x‖ₑ ^ r ∂μ ≤
        (∫⁻ q, ‖q.2‖ₑ ^ r ∂(μ ⊗ₘ κ)) / ENNReal.ofReal (min p (1 - p)) := by sorry

end StoneRegression.Quantile
