-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P54_elementary_rate_estimate
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P54.elementary_rate_estimate
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:45:47.703213+00:00
-- url     : https://prove2.me/theorems/25233542-9359-4468-b636-77e48ee2b0e9
-- title:
--   Appendix A, equation A3: elementary rate estimate
-- statement:
--   For $-1<\xi\le1$, the natural logarithm satisfies
--
--   $$\frac{\xi-\ln(1+\xi)}{2\ln2}\ge\frac{\xi^2}{12\ln2}.$$
--
--   At $\xi=-1$ the left side is defined as $+\infty$, so the same extended-value inequality holds on the whole printed interval $[-1,1]$. This elementary rate estimate is the source's equation A3; it does not evaluate the undefined real logarithm at zero.
-- source:
--   Remote preparation of quantum states, arXiv:quant-ph/0307100v3, PDF p. 14, Appendix A, equation A3: elementary rate estimate

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

/-- Equation A3, PDF p.14, including its extended-value left endpoint. -/
theorem elementary_rate_estimate (xi : ℝ) (hLower : -1 ≤ xi) (hUpper : xi ≤ 1) :
    ((xi ^ 2 / (12 * Real.log 2) : ℝ) : EReal) ≤ elementaryRate xi := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P54

end
