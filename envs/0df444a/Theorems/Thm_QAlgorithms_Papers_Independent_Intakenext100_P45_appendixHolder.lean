-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P45_appendixHolder
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P45.appendixHolder
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:22:49.353992+00:00
-- url     : https://prove2.me/theorems/8c1f376b-1304-4d4a-9fc1-041366175b9f
-- title:
--   Appendix A, Theorem 6
-- statement:
--   Let $A,B$ be positive trace-class operators on a complex Hilbert space with a finite or countable orthonormal basis. For $0\le s\le1$,
--
--   $$\|A^{1/2}B^{1/2}\|_1\le[\operatorname{Tr}(A^sB^{1-s})]^{1/2}(\operatorname{Tr}A)^{(1-s)/2}(\operatorname{Tr}B)^{s/2}.$$
--
--   The ordinary traces are finite; arbitrary traces, singular operators and the zero operator are allowed. Endpoint powers use the identity, so this form avoids undefined interior Hölder exponents.
-- source:
--   Asymptotic Error Rates in Quantum Hypothesis Testing, arXiv:0708.4282v1, PDF p. 32, Appendix A, Theorem 6

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

/-- arXiv:0708.4282v1, PDF pp.17,32: Appendix A, Theorem 6. -/
theorem appendixHolder {K : Type} [Countable K] (b : HilbertBasis K ℂ H)
    (A B : H →L[ℂ] H) (hA : A.IsPositive) (hB : B.IsPositive)
    (htA : IsTraceClass A) (htB : IsTraceClass B)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    traceNormValue ((cfc Real.sqrt A).comp (cfc Real.sqrt B)) ≤
      Real.sqrt (operatorTrace b ((cfc (fun x : ℝ => x^s) A).comp
        (cfc (fun x : ℝ => x^(1-s)) B))).re *
      ((operatorTrace b A).re)^((1-s)/2) * ((operatorTrace b B).re)^(s/2) := by sorry

end HilbertAppendix

end QAlgorithms.Papers.Independent.Intakenext100.P45

end
