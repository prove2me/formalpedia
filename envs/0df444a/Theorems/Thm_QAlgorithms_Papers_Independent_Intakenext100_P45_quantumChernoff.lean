-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P45_quantumChernoff
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P45.quantumChernoff
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:55:58.863576+00:00
-- url     : https://prove2.me/theorems/f571540b-0bed-46f2-b3c7-72d50b176472
-- title:
--   Theorem 1, quantum Chernoff bound (seed announced in abstract)
-- statement:
--   Let $\rho,\sigma$ be density operators on a finite-dimensional complex Hilbert space, and let fixed priors $\pi_0,\pi_1>0$ sum to one. Let $P^*_{e,n}$ be the minimum weighted error over all joint binary effects on $n$ IID copies. Then the extended rate limit exists and
--
--   $$\lim_{n\to\infty}-\frac1n\log P^*_{e,n}=-\log\inf_{0\le s\le1}\operatorname{Tr}(\rho^{1-s}\sigma^s).$$
--
--   Natural logarithms are used and $-\log0=+\infty$. This identifies the optimal symmetric testing exponent, including orthogonal states.
-- source:
--   Asymptotic Error Rates in Quantum Hypothesis Testing, arXiv:0708.4282v1, PDF p. 1, Theorem 1, quantum Chernoff bound (seed announced in abstract)

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

/-- arXiv:0708.4282v1, PDF pp.1,9,12,13: Theorem 1, quantum Chernoff bound (seed announced in abstract). -/
theorem quantumChernoff (rho sigma : Mat I)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (p0 p1 : ℝ) (h0 : 0 < p0) (h1 : 0 < p1) (hp : p0+p1=1) :
    HasRate (fun k => helstromError (copies (k+1) rho) (copies (k+1) sigma) p0 p1)
      (chernoffDistance rho sigma) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P45

end
