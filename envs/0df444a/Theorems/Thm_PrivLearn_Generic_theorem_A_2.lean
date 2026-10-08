-- Prove2me | Theorems.Thm_PrivLearn_Generic_theorem_A_2
-- name    : PrivLearn.Generic.theorem_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:46:18.097005+00:00
-- url     : https://prove2.me/theorems/e87fb8fe-a0cd-4f74-a5c9-2ac77c2ec82b
-- title:
--   Theorem A.2 — real-valued additive Chernoff–Hoeffding bound
-- statement:
--   Let $X_1,\dots,X_n$ be independent, identically distributed real random variables on a probability space, with $\mathbb E[X_i]=\mu$ and $a\le X_i\le b$ for all $i$. Then for every $\delta>0$,
--
--   $$\Pr\left[\,\left|\frac{\sum_i X_i}{n}-\mu\right|\ge\delta\right]\le 2\exp\left(\frac{-2\delta^2 n}{(b-a)^2}\right).$$
--
--   This is the concentration inequality behind the uniform convergence step in the proof of Theorem 3.4: applied to the indicators $X_i=\mathbf 1[h(x_i)\neq y_i]$ it bounds the deviation of the training error of a fixed hypothesis from its true error.
--
--   **Formalization Note.** The variables are indexed by `Fin n`, assumed measurable, mutually independent and pairwise identically distributed, with values in $[a,b]$ at every point. The statement makes no assumption $n\ge1$ or $a<b$: for $n=0$ the average is $0$ by Lean's convention $x/0=0$ and the bound is $2$; for $a=b$ the exponent is $0$ (division by zero is $0$) and the bound is $2$; in both cases the inequality is trivially true, as it is in the paper's reading.
-- source:
--   Kasiviswanathan, Lee, Nissim, Raskhodnikova and Smith, What Can We Learn Privately?, arXiv:0803.0924v3, p. 35, Appendix A, Theorem A.2

import Mathlib

open MeasureTheory ProbabilityTheory

namespace PrivLearn.Generic

/-- Theorem A.2 (p. 35, real-valued additive Chernoff–Hoeffding bound). Let `X_0, …, X_{n−1}` be
i.i.d. real random variables with mean `μ` and values in `[a, b]`. Then for every `δ > 0`,
`Pr[|(∑ᵢ Xᵢ)/n − μ| ≥ δ] ≤ 2 exp(−2δ²n/(b − a)²)`. -/
theorem theorem_A_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : Fin n → Ω → ℝ) (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i j, IdentDistrib (X i) (X j) P P)
    (μ a b : ℝ) (hmean : ∀ i, ∫ ω, X i ω ∂P = μ) (hbdd : ∀ i ω, X i ω ∈ Set.Icc a b)
    (δ : ℝ) (hδ : 0 < δ) :
    P {ω | δ ≤ |(∑ i, X i ω) / n - μ|}
      ≤ ENNReal.ofReal (2 * Real.exp (-2 * δ ^ 2 * n / (b - a) ^ 2)) := by sorry

end PrivLearn.Generic
