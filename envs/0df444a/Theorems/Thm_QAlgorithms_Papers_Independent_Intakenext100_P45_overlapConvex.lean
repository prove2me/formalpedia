-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P45_overlapConvex
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P45.overlapConvex
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:05:15.19299+00:00
-- url     : https://prove2.me/theorems/bc16b1ad-47cb-48b6-9a6a-15398bd8b664
-- title:
--   §4.4, convexity of Qs in s
-- statement:
--   For density operators $\rho,\sigma$, the unital-power overlap is convex on $[0,1]$:
--
--   $$Q_{ts_1+(1-t)s_2}\le tQ_{s_1}+(1-t)Q_{s_2}\quad(s_1,s_2,t\in[0,1]).$$
--
--   Consequently a local minimum on this interval is global. Singular inputs are allowed and can produce upward jumps at the endpoints.
-- source:
--   Asymptotic Error Rates in Quantum Hypothesis Testing, arXiv:0708.4282v1, PDF p. 18, §4.4, convexity of Qs in s

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

/-- arXiv:0708.4282v1, PDF p.18: §4.4, convexity of Qs in s. -/
theorem overlapConvex (rho sigma : Mat I)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (chernoffOverlap rho sigma) ∧
    (∀ s ∈ Set.Icc (0 : ℝ) 1,
      IsLocalMinOn (chernoffOverlap rho sigma) (Set.Icc 0 1) s →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, chernoffOverlap rho sigma s ≤ chernoffOverlap rho sigma t) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P45

end
