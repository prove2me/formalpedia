-- Prove2me | Theorems.Thm_StoneRegression_Criterion_proposition_3
-- name    : StoneRegression.Criterion.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:43:58.558336+00:00
-- url     : https://prove2.me/theorems/56a01c1a-976b-4aa9-b2e9-9ef00807aa6a
-- title:
--   Proposition 3, p. 609 — the bounds of Proposition 2 for the squared weights $W_{ni}^2$
-- statement:
--   Let $X, X_1, X_2,\dots$ be i.i.d. $\mathbb R^d$-valued with law $\mu$ and let $\{W_n\}$ be a sequence of Borel weights (of any sign) satisfying conditions (1)–(3) of Theorem 1. Suppose that there are sequences $\{M_n\}$ and $\{N_n\}$ of nonnegative constants such that
--   $$\lim_{n\to\infty} P\Big(M_n\le \sum_i W_{ni}^2(X)\le N_n\Big) = 1 .$$
--   Let $f$ be a nonnegative Borel function on $\mathbb R^d$ with $Ef(X)<\infty$. Then
--   $$\liminf_{n} E\sum_i W_{ni}^2(X)f(X_i) \ \ge\ \big(\liminf_n M_n\big)\,Ef(X)$$
--   and
--   $$\limsup_{n} E\sum_i W_{ni}^2(X)f(X_i) \ \le\ \big(\limsup_n N_n\big)\,Ef(X).$$
--
--   It is used in the $r=2$ case of Theorem 1, where the second moment of the noise part $\sum_i W_{ni}(X)(Y_i - E(Y_i\mid X_i))$ equals $E\sum_i W_{ni}^2(X)h(X_i)$ with $h(x) = E\big((Y - E(Y\mid X))^2\mid X = x\big)$.
--
--   **Formalization Note.** As in Proposition 2, all expectations and limits inferior and superior are in $[0,\infty]$. The paper does not assume nonnegative weights here, and neither does the statement. Weights are assumed jointly Borel (standing assumption).
-- source:
--   Stone (1977), Ann. Statist. 5, Proposition 3, p. 609

import Mathlib
import Definitions.Def_StoneRegression_Criterion_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace StoneRegression.Criterion

/-- Proposition 3 (Stone 1977, p. 609). Weights (of any sign) satisfying (1)–(3), constants `Mₙ, Nₙ ≥ 0`
with `P(Mₙ ≤ ∑ᵢ W²_{ni}(X) ≤ Nₙ) → 1`, and a nonnegative Borel `f` with `Ef(X) < ∞`. Then
`liminf E ∑ᵢ W²_{ni}(X) f(Xᵢ) ≥ (liminf Mₙ) Ef(X)` and `limsup E ∑ᵢ W²_{ni}(X) f(Xᵢ) ≤ (limsup Nₙ) Ef(X)`,
all in `ℝ≥0∞`. -/
theorem proposition_3 {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (W : WeightSeq d) (hW : MeasurableWeights W)
    (h1 : ∃ C : ℝ≥0, 1 ≤ C ∧ Cond1 μ W C) (h2 : ∃ D : ℝ, 1 ≤ D ∧ Cond2 μ W D) (h3 : Cond3 μ W)
    (M N : ℕ → ℝ≥0)
    (hMN : Tendsto (fun n => xLaw μ {ω | (M n : ℝ) ≤ ∑ i : Fin n, wAt W n ω i ^ 2 ∧
        ∑ i : Fin n, wAt W n ω i ^ 2 ≤ (N n : ℝ)}) atTop (𝓝 1))
    (f : EuclideanSpace ℝ (Fin d) → ℝ≥0) (hf : Measurable f) (hfi : ∫⁻ x, f x ∂μ < ∞) :
    liminf (fun n => (M n : ℝ≥0∞)) atTop * ∫⁻ x, f x ∂μ ≤
        liminf (fun n => ∫⁻ ω, ∑ i : Fin n,
          ENNReal.ofReal (wAt W n ω i ^ 2) * (f (ω (i.val + 1)) : ℝ≥0∞) ∂(xLaw μ)) atTop ∧
      limsup (fun n => ∫⁻ ω, ∑ i : Fin n,
          ENNReal.ofReal (wAt W n ω i ^ 2) * (f (ω (i.val + 1)) : ℝ≥0∞) ∂(xLaw μ)) atTop ≤
        limsup (fun n => (N n : ℝ≥0∞)) atTop * ∫⁻ x, f x ∂μ := by sorry

end StoneRegression.Criterion
