-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P45_appendixTraceNorm
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P45.appendixTraceNorm
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:23:30.751664+00:00
-- url     : https://prove2.me/theorems/dfc134b2-f5af-46c0-a96c-43a829630a53
-- title:
--   Appendix A, Theorem 7
-- statement:
--   For arbitrary positive trace-class operators $A,B$ on a finite- or countably infinite-dimensional complex Hilbert space,
--
--   $$\|A-B\|_1^2+4\bigl(\operatorname{Tr}(A^{1/2}B^{1/2})\bigr)^2\le\bigl(\operatorname{Tr}(A+B)\bigr)^2.$$
--
--   No normalization or invertibility is assumed. The overlap is the plain real trace of the product of square roots, rather than its trace norm.
-- source:
--   Asymptotic Error Rates in Quantum Hypothesis Testing, arXiv:0708.4282v1, PDF p. 32, Appendix A, Theorem 7

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

section HilbertAppendix

open QAlgorithms.Papers.Independent.Dependency50.P13
  (IsTraceClass operatorTrace traceNormValue)

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- arXiv:0708.4282v1, PDF pp.17,32,33: Appendix A, Theorem 7. -/
theorem appendixTraceNorm {K : Type} [Countable K] (b : HilbertBasis K ℂ H)
    (A B : H →L[ℂ] H) (hA : A.IsPositive) (hB : B.IsPositive)
    (htA : IsTraceClass A) (htB : IsTraceClass B) :
    (traceNormValue (A-B))^2 +
      4*((operatorTrace b ((cfc Real.sqrt A).comp (cfc Real.sqrt B))).re)^2 ≤
      ((operatorTrace b (A+B)).re)^2 := by sorry

end HilbertAppendix

end QAlgorithms.Papers.Independent.Intakenext100.P45

end
