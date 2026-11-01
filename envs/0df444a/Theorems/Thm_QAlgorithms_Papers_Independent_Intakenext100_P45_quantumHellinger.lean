-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P45_quantumHellinger
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P45.quantumHellinger
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:09:36.673989+00:00
-- url     : https://prove2.me/theorems/6c48105b-6df6-49bd-bac9-e7f0773c11c8
-- title:
--   §4.8, quantum minimizing condition (38)–(40)
-- statement:
--   For invertible finite-dimensional densities $\rho,\sigma$, let $Q_s=\operatorname{Tr}(\rho^{1-s}\sigma^s)$ and $\rho_s=\rho^{1-s}\sigma^s/Q_s$. Then
--
--   $$Q_s'=-\operatorname{Tr}(\rho^{1-s}\sigma^s\log\rho)+\operatorname{Tr}(\rho^{1-s}\sigma^s\log\sigma).$$
--
--   A minimizer exists on $[0,1]$; a parameter minimizes exactly when the two traces agree, equivalently when $S_{\rm gen}(\rho_s\|\rho)=S_{\rm gen}(\rho_s\|\sigma)$. Here $\rho_s$ can be non-self-adjoint; its logarithm is transported by similarity from the positive definite sandwich, and $S_{\rm gen}(X\|Y)=\operatorname{Re}\operatorname{Tr}X(\log X-\log Y)$. No equality of these values with the Chernoff distance is asserted.
-- source:
--   Asymptotic Error Rates in Quantum Hypothesis Testing, arXiv:0708.4282v1, PDF p. 20, §4.8, quantum minimizing condition (38)–(40)

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

/-- arXiv:0708.4282v1, PDF pp.19,20: §4.8, quantum minimizing condition (38)–(40). -/
theorem quantumHellinger (rho sigma : Mat I)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hir : IsUnit rho) (his : IsUnit sigma) :
    (∀ s ∈ Set.Icc (0 : ℝ) 1,
      deriv (chernoffOverlap rho sigma) s =
        -(positiveMatrixRpow rho (1-s)*positiveMatrixRpow sigma s*cfc Real.log rho).trace.re +
         (positiveMatrixRpow rho (1-s)*positiveMatrixRpow sigma s*cfc Real.log sigma).trace.re ∧
      ((∀ t ∈ Set.Icc (0 : ℝ) 1, chernoffOverlap rho sigma s ≤ chernoffOverlap rho sigma t) ↔
        (positiveMatrixRpow rho (1-s)*positiveMatrixRpow sigma s*cfc Real.log rho).trace =
          (positiveMatrixRpow rho (1-s)*positiveMatrixRpow sigma s*cfc Real.log sigma).trace) ∧
      ((positiveMatrixRpow rho (1-s)*positiveMatrixRpow sigma s*cfc Real.log rho).trace =
          (positiveMatrixRpow rho (1-s)*positiveMatrixRpow sigma s*cfc Real.log sigma).trace ↔
        arcRelative rho sigma rho s = arcRelative rho sigma sigma s)) ∧
    (∃ s ∈ Set.Icc (0 : ℝ) 1,
      (∀ t ∈ Set.Icc (0 : ℝ) 1, chernoffOverlap rho sigma s ≤ chernoffOverlap rho sigma t) ∧
      arcRelative rho sigma rho s = arcRelative rho sigma sigma s) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P45

end
