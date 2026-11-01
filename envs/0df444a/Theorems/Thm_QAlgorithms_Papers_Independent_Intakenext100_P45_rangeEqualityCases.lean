-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P45_rangeEqualityCases
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P45.rangeEqualityCases
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:03:51.083365+00:00
-- url     : https://prove2.me/theorems/b8703bad-494c-4248-a10c-9e80f75a0e7b
-- title:
--   §4.2, range and equality cases
-- statement:
--   For density operators $\rho,\sigma$, the coefficient and extended Chernoff distance obey
--
--   $$0\le Q\le1,\quad Q=1\iff\rho=\sigma,\quad Q=0\iff\operatorname{Tr}(\rho\sigma)=0,$$
--   $$0\le\xi_{\rm QCB},\quad\xi_{\rm QCB}=0\iff\rho=\sigma,\quad\xi_{\rm QCB}=+\infty\iff\operatorname{Tr}(\rho\sigma)=0.$$
--
--   Every value in $[0,+\infty]$ occurs for a pair of qubit states. This range claim allows varying states in dimension two; it does not impose that range in dimension one.
-- source:
--   Asymptotic Error Rates in Quantum Hypothesis Testing, arXiv:0708.4282v1, PDF p. 17, §4.2, range and equality cases

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

/-- arXiv:0708.4282v1, PDF p.17: §4.2, range and equality cases. -/
theorem rangeEqualityCases (rho sigma : Mat I)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    0 ≤ chernoffInfimum rho sigma ∧ chernoffInfimum rho sigma ≤ 1 ∧
    (chernoffInfimum rho sigma = 1 ↔ rho=sigma) ∧
    (chernoffInfimum rho sigma = 0 ↔ (rho*sigma).trace=0) ∧
    0 ≤ chernoffDistance rho sigma ∧
    (chernoffDistance rho sigma = 0 ↔ rho=sigma) ∧
    (chernoffDistance rho sigma = ⊤ ↔ (rho*sigma).trace=0) ∧
    (∀ d : EReal, 0 ≤ d → ∃ r s : Mat (Fin 2),
      IsDensityMatrix r ∧ IsDensityMatrix s ∧ chernoffDistance r s=d) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P45

end
