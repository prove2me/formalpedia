-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P40_gaussian_noise
-- name    : QAlgorithms.Papers.Independent.Extend50.P40.gaussian_noise
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:15:01.356729+00:00
-- url     : https://prove2.me/theorems/ccdf4ddd-506e-4053-911c-850c981c79d9
-- title:
--   §III.A Eqs.(55),(61): optimal Gaussian added-noise bound
-- statement:
--   Let $1\le N<M$ on the full oscillator Fock spaces with $[x,p]=i$ and vacuum variance 1/2. A fixed Stinespring isometry has Bose-supported coherent-input outputs and all single-clone marginals given by the additive isotropic Gaussian mixture (53), with added quadrature variance $t\ge0$. Then
--
--   $$
--   t\ge\frac1N-\frac1M.
--   $$
--
--   An isometry in this exact class attains equality. This is a Gaussian added-noise bound, not a single-copy fidelity optimum among all non-Gaussian cloners.
-- source:
--   Quantum cloning, arXiv:quant-ph/0511088v1, PDF p. 15, §III.A Eqs.(55),(61): optimal Gaussian added-noise bound

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P40

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P40

open QAlgorithms

open scoped Matrix ComplexOrder ComplexConjugate BigOperators Topology

open MeasureTheory Filter

open scoped Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P12 (sigma)

open QAlgorithms.Papers.Independent.Dependency50.P48 (pureFidelity)

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Support21.P16
  (CloneMap IsBoseInputChannel coherentTensor tensorWithIdentity canonicalCloner
   HasBoseOutput HasBlackCowCoefficient canonicalCoefficient oneMixed)

open QAlgorithms.Papers.Independent.Renew46.P45
  (TensorMat boseProjector siteObservable)

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Claimed50.P30
  (ModeHilbert ModeOperator IsModeDensity FockWeylSystem)

open QAlgorithms.Papers.Independent.Renew46.P41
  (coherentProduct NormalizedCoherent IsReducedDensity FockCanonicalAction
   ModeUnitary twoModeAmplifierQuadratures modeMixingQuadratures embeddedOpticalBeam
   displacedThermal cloneNoise cloneFidelity)

open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentProjector)

/-- III.A, PDF pp.15–16 Eqs.(55),(61): the optimal ADDED quadrature variance
within the source's symmetric Gaussian class, with an actual attaining channel. -/
theorem gaussian_noise (N M : ℕ) (hN : 1 ≤ N) (hNM : N < M) :
    (∀ (V : OscillatorCloner N M) (t : ℝ), SymmetricGaussian V t →
      1 / (N : ℝ) - 1 / (M : ℝ) ≤ t) ∧
    ∃ V : OscillatorCloner N M, SymmetricGaussian V (1 / (N : ℝ) - 1 / (M : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P40

end
