-- Prove2me | Theorems.Thm_StoneRegression_Criterion_proposition_2
-- name    : StoneRegression.Criterion.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:43:52.580695+00:00
-- url     : https://prove2.me/theorems/c2af25d9-f96e-48e5-90d0-f5aaba6454d3
-- title:
--   Proposition 2, p. 608 — liminf/limsup bounds on $E\sum_i W_{ni}(X)f(X_i)$ for nonnegative weights
-- statement:
--   Let $X, X_1, X_2,\dots$ be i.i.d. $\mathbb R^d$-valued with law $\mu$ and let $\{W_n\}$ be a sequence of nonnegative Borel weights satisfying conditions (1)–(3) of Theorem 1. Suppose that there are sequences $\{M_n\}$ and $\{N_n\}$ of nonnegative constants such that
--   $$\lim_{n\to\infty} P\Big(M_n\le \sum_i W_{ni}(X)\le N_n\Big) = 1 .$$
--   Let $f$ be a nonnegative Borel function on $\mathbb R^d$ with $Ef(X)<\infty$. Then
--   $$\liminf_{n} E\sum_i W_{ni}(X)f(X_i) \ \ge\ \big(\liminf_n M_n\big)\,Ef(X)$$
--   and
--   $$\limsup_{n} E\sum_i W_{ni}(X)f(X_i) \ \le\ \big(\limsup_n N_n\big)\,Ef(X).$$
--
--   The proposition controls the first moments of weighted sums by the total mass of the weights; Proposition 3 applies it to the squared weights in the $r=2$ step of Theorem 1.
--
--   **Formalization Note.** All expectations, limits inferior and superior are taken in $[0,\infty]$ (a $\limsup$ of the $N_n$ may be $+\infty$), with the convention $0\cdot\infty = 0$ of $[0,\infty]$; with $Ef(X) = 0$ both sides of the upper bound vanish. Weights are assumed jointly Borel (standing assumption).
-- source:
--   Stone (1977), Ann. Statist. 5, Proposition 2, p. 608; proof p. 608

import Mathlib
import Definitions.Def_StoneRegression_Criterion_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace StoneRegression.Criterion

/-- Proposition 2 (Stone 1977, p. 608). Nonnegative weights satisfying (1)–(3), constants `Mₙ, Nₙ ≥ 0` with
`P(Mₙ ≤ ∑ᵢ W_{ni}(X) ≤ Nₙ) → 1`, and a nonnegative Borel `f` with `Ef(X) < ∞`. Then
`liminf E ∑ᵢ W_{ni}(X) f(Xᵢ) ≥ (liminf Mₙ) Ef(X)` and `limsup E ∑ᵢ W_{ni}(X) f(Xᵢ) ≤ (limsup Nₙ) Ef(X)`,
all in `ℝ≥0∞` (the limits inferior and superior may be `+∞`). -/
theorem proposition_2 {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (W : WeightSeq d) (hW : MeasurableWeights W) (hnn : Nonneg W)
    (h1 : ∃ C : ℝ≥0, 1 ≤ C ∧ Cond1 μ W C) (h2 : ∃ D : ℝ, 1 ≤ D ∧ Cond2 μ W D) (h3 : Cond3 μ W)
    (M N : ℕ → ℝ≥0)
    (hMN : Tendsto (fun n => xLaw μ {ω | (M n : ℝ) ≤ ∑ i : Fin n, wAt W n ω i ∧
        ∑ i : Fin n, wAt W n ω i ≤ (N n : ℝ)}) atTop (𝓝 1))
    (f : EuclideanSpace ℝ (Fin d) → ℝ≥0) (hf : Measurable f) (hfi : ∫⁻ x, f x ∂μ < ∞) :
    liminf (fun n => (M n : ℝ≥0∞)) atTop * ∫⁻ x, f x ∂μ ≤
        liminf (fun n => ∫⁻ ω, ∑ i : Fin n,
          ENNReal.ofReal (wAt W n ω i) * (f (ω (i.val + 1)) : ℝ≥0∞) ∂(xLaw μ)) atTop ∧
      limsup (fun n => ∫⁻ ω, ∑ i : Fin n,
          ENNReal.ofReal (wAt W n ω i) * (f (ω (i.val + 1)) : ℝ≥0∞) ∂(xLaw μ)) atTop ≤
        limsup (fun n => (N n : ℝ≥0∞)) atTop * ∫⁻ x, f x ∂μ := by sorry

end StoneRegression.Criterion
