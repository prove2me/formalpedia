-- Prove2me | Theorems.Thm_STOC2027BoolCSP_Approximation_theorem_4_1
-- name    : STOC2027BoolCSP.Approximation.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:53:28.060518+00:00
-- url     : https://prove2.me/theorems/8f9cd56c-70d2-4dc6-838b-4287abf154f4
-- title:
--   Theorem 4.1 — centered product inequality (Mulgund)
-- statement:
--   Let $R$ be an $m\times m$ correlation matrix and $X\sim N(0,R)$. Let $f_1,\dots,f_m:\mathbb R\to[0,\infty)$ be bounded and log-concave, and suppose that for $Z\sim N(0,1)$
--   $$\mathbb E f_i(Z)>0,\qquad \mathbb E[Zf_i(Z)]=0\qquad(i=1,\dots,m).$$
--   Then
--   $$\mathbb E\prod_{i=1}^m f_i(X_i)\;\ge\;\prod_{i=1}^m\mathbb E f_i(Z).$$
--
--   The correlation matrix may be singular and may have negative entries. The functions need not be symmetric, only centered in the first-moment sense. The inequality is the input to Bakshi's variational bound (Proposition 4.2).
--
--   **Formalization Note** Log-concavity is the published `ConvexOptimization.LogConcaveOn` on all of $\mathbb R$, in the power form $f(x)^af(y)^b\le f(ax+by)$, which allows zeros. Boundedness is boundedness of the range.
--
--   Differences from the source:
--
--   - encoding: X ∼ N(0,R), log-concave f_i : ℝ → [0,∞) → Mathlib multivariateGaussian 0 R; LogConcaveOn Set.univ in the rpow form, nonnegativity and BddAbove of the range as separate hypotheses; reason: standard Lean conventions; log-concavity of a nonnegative function is exactly the power-form inequality
-- source:
--   Zhijie Zheng, Yucong He, Chengzhi Xie, Approximation and Even Arity Hardness for Boolean Constraint Satisfaction, STOC 2027 submission #40 (October 2026), printed p. 7 (PDF 10), Theorem 4.1

import Mathlib
import Definitions.Def_LogConcaveOn
import Definitions.Def_STOC2027BoolCSP_Approximation_Gaussian

open MeasureTheory ProbabilityTheory

namespace STOC2027BoolCSP.Approximation

/-- Theorem 4.1 (centered product inequality of Mulgund), printed p. 7. -/
theorem theorem_4_1 (m : ℕ) (R : Matrix (Fin m) (Fin m) ℝ) (hR : IsCorrelation R)
    (f : Fin m → ℝ → ℝ) (hf_nonneg : ∀ i x, 0 ≤ f i x) (hf_bdd : ∀ i, BddAbove (Set.range (f i)))
    (hf_logconc : ∀ i, ConvexOptimization.LogConcaveOn Set.univ (f i))
    (hf_pos : ∀ i, 0 < ∫ z, f i z ∂(gaussianReal 0 1))
    (hf_center : ∀ i, ∫ z, z * f i z ∂(gaussianReal 0 1) = 0) :
    ∏ i, ∫ z, f i z ∂(gaussianReal 0 1) ≤
      ∫ x, ∏ i, f i (x i) ∂(multivariateGaussian 0 R) := by sorry

end STOC2027BoolCSP.Approximation
