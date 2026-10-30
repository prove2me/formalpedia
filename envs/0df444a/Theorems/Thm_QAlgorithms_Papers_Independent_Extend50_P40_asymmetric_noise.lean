-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P40_asymmetric_noise
-- name    : QAlgorithms.Papers.Independent.Extend50.P40.asymmetric_noise
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:16:28.584979+00:00
-- url     : https://prove2.me/theorems/a70ad786-c371-49b5-b501-11f4312edba4
-- title:
--   §III.A.2 Eqs.(62)–(63): asymmetric quadrature-noise trade-offs
-- statement:
--   Take a fixed physical oscillator 1-to-2 channel. For every coherent input suppose each output is an additive displacement mixture, with fixed centered probability laws having finite x and p second moments. Write $v_{x,j},v_{p,j}$ for these added variances, using displacement $(x+ip)/\sqrt2$. Then
--
--   $$
--   v_{x,1}v_{p,2}\ge\tfrac14,\qquad v_{p,1}v_{x,2}\ge\tfrac14.
--   $$
--
--   The actual probability-noise model and full-space channel constrain the variances. They are neither total output variances nor unconstrained numerical parameters; singular noise laws are allowed.
-- source:
--   Quantum cloning, arXiv:quant-ph/0511088v1, PDF p. 16, §III.A.2 Eqs.(62)–(63): asymmetric quadrature-noise trade-offs

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

/-- III.A.2, PDF p.16 Eqs.(62)–(63): genuine additive displacement-noise model
on a fixed physical two-output channel. This includes unequal clones and anisotropic
noise; it does not infer the result from a bound on total variances. -/
theorem asymmetric_noise (V : OscillatorCloner 1 2) (mu nu : DisplacementNoise)
    (h : ∀ alpha : ℂ,
      IsReducedDensity
        (InnerProductSpace.rankOne ℂ (V (coherentReplicas 1 alpha)) (V (coherentReplicas 1 alpha)))
        (0 : Fin 3) (noiseMixture mu alpha) ∧
      IsReducedDensity
        (InnerProductSpace.rankOne ℂ (V (coherentReplicas 1 alpha)) (V (coherentReplicas 1 alpha)))
        (1 : Fin 3) (noiseMixture nu alpha)) :
    addedX mu * addedP nu ≥ 1 / 4 ∧ addedP mu * addedX nu ≥ 1 / 4 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P40

end
