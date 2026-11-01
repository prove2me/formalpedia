-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P45_quantumClassicalComparison
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P45.quantumClassicalComparison
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:00:12.424724+00:00
-- url     : https://prove2.me/theorems/309c149e-d6f7-4674-b9a1-ad045654e022
-- title:
--   Proposition 2, quantum/classical error comparison
-- statement:
--   Let $p,q$ be the spectral-pair laws associated with density operators $\rho,\sigma$. For every orthogonal projector $P$ and positive weights $\eta_0,\eta_1$, without requiring their sum to be one,
--
--   $$\eta_0\operatorname{Tr}(P\rho)+\eta_1\operatorname{Tr}((I-P)\sigma)\ge\frac12\inf_{0\le\phi\le1}\sum_{ij}[\eta_0p_{ij}\phi_{ij}+\eta_1q_{ij}(1-\phi_{ij})].$$
--
--   The infimum ranges over every randomized classical test. This transfers classical converse bounds to joint quantum tests.
-- source:
--   Asymptotic Error Rates in Quantum Hypothesis Testing, arXiv:0708.4282v1, PDF p. 10, Proposition 2, quantum/classical error comparison

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

/-- arXiv:0708.4282v1, PDF pp.10,11,12: Proposition 2, quantum/classical error comparison. -/
theorem quantumClassicalComparison (rho sigma : Mat I)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (D : SpectralPair rho sigma) (P : Mat I) (hP : IsProjection P)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (1/2 : ℝ) * sInf (Set.range (classicalError (spectralP D) (spectralQ D) a b)) ≤
      bayesError rho sigma P a b := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P45

end
