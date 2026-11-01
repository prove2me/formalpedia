-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P45_sumRate
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P45.sumRate
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:20:14.528743+00:00
-- url     : https://prove2.me/theorems/35e576ba-1f08-4539-800c-3fa620592374
-- title:
--   Lemma 7, rate of a sum
-- statement:
--   Let $x_n,y_n>0$ have existing extended exponential rate limits $x_R,y_R$. Then the rate of their sum exists and
--
--   $$\lim_{n\to\infty}-\frac1n\log(x_n+y_n)=\min(x_R,y_R).$$
--
--   The sequences need not be probabilities, so negative rates and either sign of infinity are allowed.
-- source:
--   Asymptotic Error Rates in Quantum Hypothesis Testing, arXiv:0708.4282v1, PDF p. 28, Lemma 7, rate of a sum

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P45

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P45

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder ENNReal BigOperators Topology

open QAlgorithms.Papers.Independent.Information100.P07
  (support positivePart positiveProjection IsProjection)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Dependency50.P28 (logNonnegativeExtended relativeEntropy)

open QAlgorithms.Papers.Independent.Claimed50.P15 (positiveMatrixRpow)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- arXiv:0708.4282v1, PDF p.28: Lemma 7, rate of a sum. -/
theorem sumRate (x y : ℕ → ℝ) (hx : ∀ k, 0 < x k) (hy : ∀ k, 0 < y k)
    (xr yr : EReal) (hrx : HasRate x xr) (hry : HasRate y yr) :
    HasRate (fun k => x k+y k) (min xr yr) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P45

end
