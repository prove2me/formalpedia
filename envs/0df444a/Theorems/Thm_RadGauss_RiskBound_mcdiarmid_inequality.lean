-- Prove2me | Theorems.Thm_RadGauss_RiskBound_mcdiarmid_inequality
-- name    : RadGauss.RiskBound.mcdiarmid_inequality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T08:01:50.237281+00:00
-- url     : https://prove2.me/theorems/3320351c-ed84-4370-8d13-07b29fd1ffa6
-- title:
--   Theorem 9 — McDiarmid's inequality $P\{f-\mathbf Ef\ge t\}\le e^{-2t^2/\sum_i c_i^2}$
-- statement:
--   Let $X_1, \dots, X_n$ be independent random variables taking values in a measurable space $A$, where $X_i$ has law $\mu_i$ (the laws need not be equal). Let $f : A^n \to \mathbb R$ be a measurable function with bounded differences: there are constants $c_1, \dots, c_n$ such that for every $i$,
--
--   $$\sup_{x_1, \dots, x_n,\, x'_i \in A}\bigl|f(x_1, \dots, x_n) - f(x_1, \dots, x_{i-1}, x'_i, x_{i+1}, \dots, x_n)\bigr| \le c_i .$$
--
--   Then for every $t > 0$,
--
--   $$P\bigl\{f(X_1, \dots, X_n) - \mathbf E f(X_1, \dots, X_n) \ge t\bigr\} \le \exp\!\Bigl(-\frac{2t^2}{\sum_{i=1}^n c_i^2}\Bigr).$$
--
--   This concentration inequality is applied twice in the proof of Theorem 8: to the uniform deviation over the centred cost class, and to the empirical mean of the cost of the fixed action $0$.
--
--   **Formalization Note** Independence is the product measure $\mu_1 \otimes \cdots \otimes \mu_n$ of probability measures on $A^n$ (`Measure.pi μ`), and the random vector is the identity. The function $f$ is assumed measurable, which the paper leaves implicit; bounded differences make it bounded, so $\mathbf E f$ is a genuine expectation. If every $c_i = 0$ the printed exponent has a zero denominator; Lean reads $x/0$ as $0$, so the bound becomes $1$, which is true (and $f$ is then constant). This is the general, not-necessarily-identically-distributed form as printed; the platform's `StabGen.Uniform.mcdiarmid_inequality` is its i.i.d. special case and `UnderstandingML.mcdiarmid_inequality_pi` is a two-sided, uniform-$c$ variant.
-- source:
--   Bartlett, Mendelson, Rademacher and Gaussian Complexities: Risk Bounds and Structural Results, J. Mach. Learn. Res. 3 (2002), p. 467 (PDF p. 5), Theorem 9 (McDiarmid's Inequality)

import Mathlib

open MeasureTheory

namespace RadGauss.RiskBound

/-- **Theorem 9 (McDiarmid's inequality)** (p. 467). Let `X_1, …, X_n` be independent random
variables with values in `A` (the coordinates under the product `μ_1 ⊗ ⋯ ⊗ μ_n` of probability
measures, not necessarily equal), and let `f : A^n → ℝ` be measurable with
`|f(x) − f(x_1, …, x_{i−1}, x'_i, x_{i+1}, …, x_n)| ≤ c_i` for every `i`, `x` and `x'_i`. Then for every
`t > 0`, `P{f(X) − E f(X) ≥ t} ≤ exp(−2t² / Σ_i c_i²)`. -/
theorem mcdiarmid_inequality {A : Type*} [MeasurableSpace A] (n : ℕ)
    (μ : Fin n → Measure A) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (Fin n → A) → ℝ) (hf : Measurable f) (c : Fin n → ℝ)
    (hc : ∀ (i : Fin n) (x : Fin n → A) (a : A), |f x - f (Function.update x i a)| ≤ c i)
    (t : ℝ) (ht : 0 < t) :
    Measure.pi μ {x | t ≤ f x - ∫ y, f y ∂(Measure.pi μ)} ≤
      ENNReal.ofReal (Real.exp (-2 * t ^ 2 / ∑ i, c i ^ 2)) := by sorry

end RadGauss.RiskBound
