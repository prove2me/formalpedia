-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P45_positivePartTraceInequality
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P45.positivePartTraceInequality
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:01:37.708991+00:00
-- url     : https://prove2.me/theorems/9c60feb7-d4da-497e-b179-79a94625c40c
-- title:
--   Lemma 2, positive-part trace inequality
-- statement:
--   For positive semidefinite matrices $A,B$, $0\le t\le1$, and the strict-positive projector $P$ of $A-B$,
--
--   $$\operatorname{Tr}[PB(A^t-B^t)]\ge0.$$
--
--   Both endpoints and singular inputs are included. This is the positive-part inequality used to establish the main trace inequality.
-- source:
--   Asymptotic Error Rates in Quantum Hypothesis Testing, arXiv:0708.4282v1, PDF p. 14, Lemma 2, positive-part trace inequality

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

/-- arXiv:0708.4282v1, PDF pp.14,15,16: Lemma 2, positive-part trace inequality. -/
theorem positivePartTraceInequality (A B : Mat I) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ (positiveProjection (A-B) * B * (positiveMatrixRpow A t-positiveMatrixRpow B t)).trace.re := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P45

end
