-- Prove2me | Theorems.Thm_RadGauss_LipschitzGaussian_theorem_16
-- name    : RadGauss.LipschitzGaussian.theorem_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T09:06:15.365428+00:00
-- url     : https://prove2.me/theorems/a2da609e-6c4a-4173-ba3f-aa86a47ad549
-- title:
--   Theorem 16 — G_n(g(F_1,…,F_k)) ≤ 2 Σ_j G_n(F_j) for a fixed boolean function g
-- statement:
--   Let $\mu$ be a probability measure on $\mathcal X$ and let $G_n$ denote the Gaussian complexity with respect to an i.i.d. sample of size $n$ from $\mu$ (Definition 2). Let $k \ge 1$, let $g : \{\pm1\}^k \to \{\pm1\}$ be a fixed boolean function, and let $F_1, \dots, F_k$ be classes of $\{\pm1\}$-valued functions on $\mathcal X$. Write $g(F_1, \dots, F_k) = \{x \mapsto g(f_1(x), \dots, f_k(x)) : f_j \in F_j\}$. Then
--
--   $$
--   G_n\bigl(g(F_1, \dots, F_k)\bigr) \le 2 \sum_{j=1}^k G_n(F_j).
--   $$
--
--   The Gaussian complexity of any fixed boolean combination of classes (intersections, unions, majority votes, …) is thus controlled by the sum of the complexities of the components, with a constant independent of $g$ and of $k$.
--
--   **Formalization Note** $\{\pm1\}$ is encoded as $\mathbb Z^\times$ coerced to $\mathbb R$. Two hypotheses are added. (i) $k \ge 1$: for $k = 0$ the boolean function is a constant $\pm1$, the right side is $0$, and the Gaussian complexity of a constant class is $\mathbb E\,\frac2n|\sum_i g_i| > 0$, so the printed statement fails; the paper tacitly assumes $k\ge1$. (ii) For each $j$, the empirical Gaussian complexity $\hat G_n(F_j)$ is an almost-everywhere measurable function of the sample; the complexities are lower Lebesgue integrals in $[0,\infty]$, and without this guard the expectation of the sum $\sum_j \hat G_n(F_j)$ need not split into the sum of expectations. The paper does not discuss measurability. No finiteness or boundedness of the classes is assumed.
-- source:
--   Bartlett, Mendelson, Rademacher and Gaussian Complexities: Risk Bounds and Structural Results, J. Mach. Learn. Res. 3 (2002), p. 472 (PDF p. 10), Theorem 16

import Mathlib
import Definitions.Def_RadGauss_LipschitzGaussian_GaussianComplexity
import Definitions.Def_RadGauss_LipschitzGaussian_Classes

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RadGauss.LipschitzGaussian

/-- **Theorem 16** (p. 472): for a fixed boolean function `g : {±1}^k → {±1}` (`k ≥ 1`) and
classes `F_1, …, F_k` of `{±1}`-valued functions on `𝒳`,
`G_n(g(F_1, …, F_k)) ≤ 2 Σ_j G_n(F_j)`, the Gaussian complexities taken with respect to a
probability measure `μ` on `𝒳`. The empirical complexities `Ĝ_n(F_j)` are assumed
almost-everywhere measurable functions of the sample. -/
theorem theorem_16 {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    {k : ℕ} (hk : 0 < k) (g : (Fin k → ℤˣ) → ℤˣ) (F : Fin k → Set (X → ℤˣ)) (n : ℕ)
    (hmeas : ∀ j, AEMeasurable (empiricalGaussian n (signClass (F j)))
      (Measure.pi fun _ : Fin n => μ)) :
    gaussianComplexity μ n (boolComb g F) ≤
      2 * ∑ j, gaussianComplexity μ n (signClass (F j)) := by sorry

end RadGauss.LipschitzGaussian
