-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P37_nonGaussianLinearChannel
-- name    : QAlgorithms.Papers.Independent.Advance50.P37.nonGaussianLinearChannel
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:42:15.671182+00:00
-- url     : https://prove2.me/theorems/08d2a1eb-ff1d-4ae7-9d34-24363d67cd1b
-- title:
--   A physical linear channel with non-Gaussian added noise
-- statement:
--   There exists a linear quantum channel that does not preserve Gaussianity. More concretely, for any real $a>0$ define the full one-mode trace-class channel
--
--   $$
--   \Phi_a(\rho)=\tfrac12D(a)\rho D(a)^\dagger+\tfrac12D(-a)\rho D(-a)^\dagger.
--   $$
--
--   This map is completely positive and trace preserving. It has a controlled-displacement unitary dilation with a fixed independent fair classical coin. In the accepted $[Q,P]=i$ coordinates, its exact Heisenberg Weyl action is $U^\dagger(W(v)\otimes I)U=W(v)\otimes\exp(i v_Q B_Q)$, where $B_Q$ has coin eigenvalues $\pm\sqrt2a$ and $B_P=0$. Tracing the same dilation gives $\Phi_a$ for every input density. Equivalently, in the source's quadratures, $X_{\rm out}=X_{\rm in}+B_X$, $P_{\rm out}=P_{\rm in}$ with $B_X=\pm2a$ independent of the input.
--
--   Every input with finite second moments retains its mean and its shot-noise covariance changes by
--
--   $$
--   \Gamma_{\rm out}=\Gamma_{\rm in}+\operatorname{diag}(4a^2,0).
--   $$
--
--   Vacuum is a normalized Gaussian input, whereas $\Phi_a(|0\rangle\langle0|)$ is normalized and is not Gaussian for any mean or covariance. This witnesses the Appendix's modest existential claim with actual densities, a physical dilation, and centered finite input-uncorrelated noise; it does not classify all linear channels.
-- source:
--   Long distance quantum key distribution with continuous variables, arXiv:1005.0328v3, PDF p. 11, Appendix: linear quantum channels need not be Gaussian

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P37

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Advance50.P37

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Gap48.P26 (totalPhotons)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (IsDensity IsBarycenter IsTraceClassChannel productCoeff)

open QAlgorithms.Papers.Independent.Claimed50.P19
  (FockIndex DensityKernel Cov standardFormCovariance vacuumKernel productWeyl weylArgument)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (unitaryCoeff conjugateKernel boundedUnitaryConjugation partialRight)

open QAlgorithms.Papers.Independent.Support50.P14 (CompleteMoments GaussianAt)

open QAlgorithms.Papers.Independent.Renew46.P39 (squeezedVacuum)

open QAlgorithms.Papers.Independent.Renew46.P41
  (coherentProductCoefficient NormalizedCoherent)

/-- PDF p.11, Appendix after Eq.(5): a physical linear channel can fail to
preserve Gaussianity. Nonzero symmetric binary displacement is an explicit
witness. Its actual dilation obeys the Heisenberg additive-noise Weyl law,
with fixed independent centered finite noise, and its vacuum output is
non-Gaussian. A covariance-only witness is not substituted. -/
theorem nonGaussianLinearChannel (a : ℝ) (ha : 0 < a) :
    IsTraceClassChannel (binaryDisplacementChannel a) ∧
    IsDensity fairNoiseCoin ∧
    (∃ U : Hilbert (FockIndex 1 × Bool) ≃ₗᵢ[ℂ] Hilbert (FockIndex 1 × Bool),
      unitaryCoeff U = controlledDisplacementKernel a ∧
      (∀ v, boundedUnitaryConjugation U.symm (carrierWeylWithCoin v) =
        noisyCarrierWeyl a v) ∧
      (∀ rho : DensityKernel 1, IsDensity rho →
        binaryDisplacementChannel a rho =
          partialRight (boundedUnitaryConjugation U (productCoeff rho fairNoiseCoin)))) ∧
    (∀ (rho : DensityKernel 1) (d : (Fin 1 × Fin 2) → ℝ) (gamma : Cov 1),
      IsDensity rho → CompleteMoments rho d gamma →
      CompleteMoments (binaryDisplacementChannel a rho) d (gamma + binaryNoiseCovariance a)) ∧
    IsDensity (vacuumKernel 1) ∧ GaussianAt (vacuumKernel 1) 0 1 ∧
    IsDensity (binaryDisplacementChannel a (vacuumKernel 1)) ∧
    (∀ (d : (Fin 1 × Fin 2) → ℝ) (gamma : Cov 1),
      ¬ GaussianAt (binaryDisplacementChannel a (vacuumKernel 1)) d gamma) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P37

end
