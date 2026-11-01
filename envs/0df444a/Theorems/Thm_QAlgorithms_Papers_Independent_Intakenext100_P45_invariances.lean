-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P45_invariances
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P45.invariances
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:07:15.110881+00:00
-- url     : https://prove2.me/theorems/814a3e68-9b04-472a-ae93-b943e24744de
-- title:
--   §4.6, unitary and ancilla invariances
-- statement:
--   For finite-dimensional density operators $\rho,\sigma$, a unitary $U$, and any ancillary density operator $\tau$,
--
--   $$Q(U\rho U^*,U\sigma U^*)=Q(\rho,\sigma),\qquad Q(\rho\otimes\tau,\sigma\otimes\tau)=Q(\rho,\sigma).$$
--
--   The ancilla may be singular and have any finite dimension. These invariances support channel monotonicity.
-- source:
--   Asymptotic Error Rates in Quantum Hypothesis Testing, arXiv:0708.4282v1, PDF p. 18, §4.6, unitary and ancilla invariances

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

/-- arXiv:0708.4282v1, PDF p.18: §4.6, unitary and ancilla invariances. -/
theorem invariances (rho sigma : Mat I)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (U : Matrix.unitaryGroup I ℂ) (tau : Mat J) (htau : IsDensityMatrix tau) :
    chernoffInfimum ((U : Mat I)*rho*(U : Mat I)ᴴ) ((U : Mat I)*sigma*(U : Mat I)ᴴ) =
      chernoffInfimum rho sigma ∧
    chernoffInfimum (Matrix.kronecker rho tau) (Matrix.kronecker sigma tau) =
      chernoffInfimum rho sigma := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P45

end
