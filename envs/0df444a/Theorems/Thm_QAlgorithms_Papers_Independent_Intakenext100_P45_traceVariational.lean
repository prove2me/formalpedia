-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P45_traceVariational
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P45.traceVariational
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:56:46.949028+00:00
-- url     : https://prove2.me/theorems/f85d316a-da1f-4cb4-8090-5fecd03bf81e
-- title:
--   Unnumbered variational maxima (6)–(7)
-- statement:
--   For any self-adjoint finite-dimensional operator $A$, let $A_+$ be its positive part and $P_+$ the orthogonal projection onto its range. Both maxima are attained at $P_+$:
--
--   $$\operatorname{Tr}A_+=\max_{0\le X\le I}\operatorname{Tr}(AX)=\max_{P=P^*=P^2}\operatorname{Tr}(AP).$$
--
--   The zero eigenspace is excluded from $P_+$. This characterizes the optimal binary testing effect.
-- source:
--   Asymptotic Error Rates in Quantum Hypothesis Testing, arXiv:0708.4282v1, PDF p. 7, Unnumbered variational maxima (6)–(7)

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

/-- arXiv:0708.4282v1, PDF p.7: Unnumbered variational maxima (6)–(7). -/
theorem traceVariational (A : Mat I) (hA : A.IsHermitian) :
    IsProjection (positiveProjection A) ∧ IsEffect (positiveProjection A) ∧
    (A * positiveProjection A).trace.re = (positivePart A).trace.re ∧
    (∀ X : Mat I, IsEffect X → (A * X).trace.re ≤ (positivePart A).trace.re) ∧
    (∀ P : Mat I, IsProjection P → (A * P).trace.re ≤ (positivePart A).trace.re) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P45

end
