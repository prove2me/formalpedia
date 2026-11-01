-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P45_conditionalThresholds
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P45.conditionalThresholds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:18:14.404416+00:00
-- url     : https://prove2.me/theorems/749bae01-da2e-4dcd-9322-a46edda97189
-- title:
--   §5.3, thresholds and pure-state case
-- statement:
--   For a nonorthogonal density pair with overlap masses $\psi_0,\psi_1$,
--
--   $$S_\rho(\sigma\|\rho)\ge-\log\psi_0,\qquad S_\sigma(\rho\|\sigma)\ge-\log\psi_1.$$
--
--   Equality holds in one bound exactly when it holds in the other. If both states are pure then $\psi_0=\psi_1$, both equalities hold, and $e_Q(r)=+\infty$ below $-\log\psi_1$ and equals $-\log\psi_1$ at and above that threshold. All conditional divisions are protected by positive overlap.
-- source:
--   Asymptotic Error Rates in Quantum Hypothesis Testing, arXiv:0708.4282v1, PDF p. 27, §5.3, thresholds and pure-state case

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

/-- arXiv:0708.4282v1, PDF pp.26,27: §5.3, thresholds and pure-state case. -/
theorem conditionalThresholds (rho sigma : Mat I)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hpsi0 : 0 < (rho*support sigma).trace.re)
    (hpsi1 : 0 < (sigma*support rho).trace.re) :
    -Real.log (rho*support sigma).trace.re ≤ supportConditionalEntropy sigma rho ∧
    -Real.log (sigma*support rho).trace.re ≤ supportConditionalEntropy rho sigma ∧
    (supportConditionalEntropy sigma rho = -Real.log (rho*support sigma).trace.re ↔
      supportConditionalEntropy rho sigma = -Real.log (sigma*support rho).trace.re) ∧
    (densityIdempotence rho → densityIdempotence sigma →
      (rho*support sigma).trace.re=(sigma*support rho).trace.re ∧
      supportConditionalEntropy sigma rho = -Real.log (rho*support sigma).trace.re ∧
      supportConditionalEntropy rho sigma = -Real.log (sigma*support rho).trace.re ∧
      ∀ r : ℝ, 0 ≤ r → quantumExponent rho sigma r =
        if r < -Real.log (sigma*support rho).trace.re then ⊤
        else ((-Real.log (sigma*support rho).trace.re : ℝ) : EReal)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P45

end
