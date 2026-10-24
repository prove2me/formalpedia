-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P14_gaussianMaximumEntropy
-- name    : QAlgorithms.Papers.Independent.Support50.P14.gaussianMaximumEntropy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:29:40.041719+00:00
-- url     : https://prove2.me/theorems/e5506a9b-e781-4e15-ac47-2a29e1c5a186
-- title:
--   Unnumbered maximum-entropy rederivation
-- statement:
--   Let $\rho$ and $\rho_G$ be normalized density operators on finitely many nonzero full oscillator modes. Suppose $\rho$ has finite complete first and second moments and $\rho_G$ is Gaussian with the same symmetric covariance $\Gamma$. Their first moments may differ. Their von Neumann entropies, computed from the densities in nats, are finite, and
--
--   $$S(\rho)\le S(\rho_G)<\infty.$$
--
--   This recovers the maximum-entropy principle at fixed covariance. Displacement invariance explains why matching the means is unnecessary.
-- source:
--   Extremality of Gaussian quantum states, arXiv:quant-ph/0509154v1, PDF p. 1, Unnumbered maximum-entropy rederivation

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P14

noncomputable section

open Filter

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Support50.P14

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsTraceClass traceSize)

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (unitaryCoeff conjugateKernel boundedUnitaryConjugation)

open QAlgorithms.Papers.Independent.Frontier18.P07 (extendedEntropyNats)

open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

/-- Maximum entropy principle rederived on PDF p.2; statement on PDF p.1.
Means may differ. Both actual density entropies are finite under finite energy. -/
theorem gaussianMaximumEntropy {I : Type} [Fintype I] [Nonempty I]
    (rho rhoG : State (Occupation I)) (d dG : InterleavedQuadrature I → ℝ) (gamma : OscillatorCovariance I)
    (hmoments : CompleteMoments rho.coefficients d gamma)
    (hgaussian : GaussianAt rhoG.coefficients dG gamma) :
    extendedEntropyNats rho.coefficients < ⊤ ∧
    extendedEntropyNats rhoG.coefficients < ⊤ ∧
    extendedEntropyNats rho.coefficients ≤ extendedEntropyNats rhoG.coefficients := by sorry

end QAlgorithms.Papers.Independent.Support50.P14

end
