-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P54_squared_gaussian_tails
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P54.squared_gaussian_tails
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:45:03.858001+00:00
-- url     : https://prove2.me/theorems/46f06c3f-d70c-452d-800c-b93eb04b2693
-- title:
--   Appendix A, equation A2: squared-Gaussian tail bounds
-- statement:
--   Let $N\ge1$, $\sigma^2>0$, and let $Y_1,\ldots,Y_N$ be independent measurable $N(0,\sigma^2)$ variables. Write $X_i=Y_i^2$. For every $\varepsilon\ge0$,
--
--   $$\Pr\left\{\frac1N\sum_iX_i>(1+\varepsilon)\sigma^2\right\}\le2^{-N(\varepsilon-\ln(1+\varepsilon))/(2\ln2)}.$$
--
--   For $0\le\varepsilon<1$ one also has
--
--   $$\Pr\left\{\frac1N\sum_iX_i<(1-\varepsilon)\sigma^2\right\}\le2^{-N(-\varepsilon-\ln(1-\varepsilon))/(2\ln2)}.$$
--
--   For $\varepsilon\ge1$ the strict lower-tail event has probability zero. This records both displayed consequences of Lemma 23 while giving the lower logarithm its correct domain.
-- source:
--   Remote preparation of quantum states, arXiv:quant-ph/0307100v3, PDF p. 14, Appendix A, equation A2: squared-Gaussian tail bounds

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

/-- Equation A2, PDF p.14: both squared-Gaussian tails. The lower displayed logarithmic
bound has domain eps < 1; for eps ≥ 1 the strict lower-tail event is empty.
The paper's exp is base two. -/
theorem squared_gaussian_tails {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] (N : ℕ) (hN : 0 < N)
    (s2 : ℝ≥0) (hs : 0 < s2) (Y : Fin N → Omega → ℝ)
    (hMeas : ∀ i, Measurable (Y i)) (hInd : iIndepFun Y mu)
    (hLaw : ∀ i, Measure.map (Y i) mu = gaussianReal 0 s2)
    (eps : ℝ) (heps : 0 ≤ eps) :
    mu {w | (∑ i, Y i w ^ 2) / (N : ℝ) > (1 + eps) * s2} ≤
      ENNReal.ofReal ((2 : ℝ) ^ (-(N : ℝ) * (eps - Real.log (1 + eps)) / (2 * Real.log 2))) ∧
    (eps < 1 → mu {w | (∑ i, Y i w ^ 2) / (N : ℝ) < (1 - eps) * s2} ≤
      ENNReal.ofReal ((2 : ℝ) ^ (-(N : ℝ) * (-eps - Real.log (1 - eps)) / (2 * Real.log 2)))) ∧
    (1 ≤ eps → mu {w | (∑ i, Y i w ^ 2) / (N : ℝ) < (1 - eps) * s2} = 0) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P54

end
