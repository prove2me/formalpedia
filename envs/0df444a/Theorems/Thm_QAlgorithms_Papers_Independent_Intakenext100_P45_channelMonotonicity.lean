-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P45_channelMonotonicity
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P45.channelMonotonicity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:06:29.103894+00:00
-- url     : https://prove2.me/theorems/622ff501-c0b1-4dc8-9c0d-e457e9963053
-- title:
--   §4.6, monotonicity (33)
-- statement:
--   For any finite-dimensional density operators $\rho,\sigma$ and completely positive trace-preserving endomap $\Phi$,
--
--   $$Q(\Phi(\rho),\Phi(\sigma))\ge Q(\rho,\sigma).$$
--
--   The channel ranges over all normalized finite Kraus representations, hence all finite-dimensional CPTP maps. Processing cannot improve the Chernoff testing exponent.
-- source:
--   Asymptotic Error Rates in Quantum Hypothesis Testing, arXiv:0708.4282v1, PDF p. 18, §4.6, monotonicity (33)

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

/-- arXiv:0708.4282v1, PDF p.18: §4.6, monotonicity (33). -/
theorem channelMonotonicity (rho sigma : Mat I)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (Phi : Superop I I) (hPhi : IsChannel Phi) :
    chernoffInfimum rho sigma ≤ chernoffInfimum (Phi rho) (Phi sigma) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P45

end
