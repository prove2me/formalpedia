-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P45_traceInequality
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P45.traceInequality
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:00:59.928427+00:00
-- url     : https://prove2.me/theorems/24804ef0-b3d2-4d12-bb38-3274d5349e84
-- title:
--   Theorem 2, trace inequality
-- statement:
--   For arbitrary positive semidefinite finite-dimensional operators $a,b$ and $0\le s\le1$,
--
--   $$\operatorname{Tr}(a^sb^{1-s})\ge\tfrac12\operatorname{Tr}(a+b-|a-b|).$$
--
--   Equivalently, for $P$ the projector onto $\operatorname{ran}(a-b)_+$, the left side is at least $\operatorname{Tr}(Pb+(I-P)a)$. No trace normalization, invertibility, or commutation is assumed.
-- source:
--   Asymptotic Error Rates in Quantum Hypothesis Testing, arXiv:0708.4282v1, PDF p. 12, Theorem 2, trace inequality

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

/-- arXiv:0708.4282v1, PDF pp.12,13,14: Theorem 2, trace inequality. -/
theorem traceInequality (a b : Mat I) (ha : a.PosSemidef) (hb : b.PosSemidef)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (a+b).trace.re/2-traceNorm (a-b)/2 ≤ (positiveMatrixRpow a s * positiveMatrixRpow b (1-s)).trace.re ∧
    (positiveProjection (a-b) * b + (1-positiveProjection (a-b))*a).trace.re ≤
      (positiveMatrixRpow a s * positiveMatrixRpow b (1-s)).trace.re := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P45

end
