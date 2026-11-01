-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P54_squared_gaussian_cramer_transform
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P54.squared_gaussian_cramer_transform
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:44:24.360453+00:00
-- url     : https://prove2.me/theorems/61fa442f-a7fc-47bf-ac91-4a7a5aebb9b4
-- title:
--   Lemma 23: squared Gaussian Cramer transform
-- statement:
--   Let $Y\sim N(0,\sigma^2)$ with $\sigma^2>0$, and put $X=Y^2$. Define the extended log moment generating function by $\Lambda(y)=\ln\mathbb E e^{yX}$, assigning $+\infty$ to divergent exponential moments, and define $\Lambda^*(x)=\sup_{y\in\mathbb R}(yx-\Lambda(y))$. Then
--
--   $$\Lambda^*(x)=\begin{cases}\frac12\bigl[x/\sigma^2-1-\ln(x/\sigma^2)\bigr],&x>0,\\+\infty,&x\le0.\end{cases}$$
--
--   The supremum and logarithm take extended values; the positive moment integral is a nonnegative extended integral. This is the rate function used for Gaussian concentration, with zero value at the mean.
-- source:
--   Remote preparation of quantum states, arXiv:quant-ph/0307100v3, PDF p. 14, Lemma 23: squared Gaussian Cramer transform

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P54

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder NNReal ENNReal

open MeasureTheory ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P54

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble)

open QAlgorithms.Papers.Independent.Information100.P53 (fidelity)

open QAlgorithms.Papers.Independent.Dependency50.P07 (wordProb)

open QAlgorithms.Papers.Independent.Claimed50.P08 (classicalEntropy)

open QAlgorithms.Papers.Independent.Claimed50.P38 (tensorSuperop)

/-- Lemma 23, PDF p.14: full Cramer transform including x ≤ 0, where it is infinity.
The variance is strictly positive; the logarithm in this formula is natural. -/
theorem squared_gaussian_cramer_transform (s2 : ℝ≥0) (hs : 0 < s2) (x : ℝ) :
    squaredGaussianRate s2 x =
      if 0 < x then (((x / s2 - 1 - Real.log (x / s2)) / 2 : ℝ) : EReal) else ⊤ := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P54

end
