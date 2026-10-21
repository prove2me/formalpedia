-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P20_ideal_teleportation
-- name    : QAlgorithms.Papers.Independent.Renew46.P20.ideal_teleportation
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T20:24:25.845087+00:00
-- url     : https://prove2.me/theorems/9fa7b80d-b4e8-4092-8d4c-3a690ebbb498
-- title:
--   Ideal teleportation with an arbitrary probability-normalized tight unitary frame
-- statement:
--   Let $H$ be a nonzero finite-dimensional complex Hilbert space of dimension $d$, with a fixed orthonormal basis. Let $U_\omega$ be a measurable unitary family on an arbitrary probability space $(\Omega,\Sigma,\mu)$, satisfying the tight-frame convention
--
--   $$
--   \int_\Omega |U_\omega\rangle\!\rangle\langle\!\langle U_\omega|\,d\mu
--   =\frac{I_{H\otimes H}}d.
--   $$
--
--   Vectorization is unnormalized and $T$ denotes transpose in the fixed basis. Define the shared state $R=|I\rangle\!\rangle\langle\!\langle I|/d$ and Alice's joint effect density $E_\omega=d|U_\omega^T\rangle\!\rangle\langle\!\langle U_\omega^T|$. Then $R$ is a density matrix and $E_\omega$ is the density, with respect to $\mu$, of a positive, countably additive, identity-normalized POVM on the same outcome space. For every density matrix $\rho$ and every outcome $\omega$,
--
--   $$
--   \rho=U_\omega\operatorname{Tr}_{2,3}
--   \big[(R\otimes\rho)(I\otimes E_\omega)\big]U_\omega^\dagger.
--   $$
--
--   The tensor factors are Bob's resource share, Alice's resource share, and the input. Thus the identity channel is realized by Alice's joint measurement, communication of the outcome, and Bob's conditional unitary. The historical classification attributed to other papers is not part of this statement.
-- source:
--   Realization schemes for quantum instruments in finite dimensions, arXiv:0810.3211v4, PDF p. 20, §7.0.1, Eq.(98)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P20

noncomputable section

open MeasureTheory

open scoped ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator

open QAlgorithms.Papers.Independent.Dependency50.P40 (operatorKet)

namespace QAlgorithms.Papers.Independent.Renew46.P20

/-- PDF p.20, §7.0.1, Eq.(98), with an explicit source normalization correction.
Printed: Eq.(83), p.17, has frame integral I tensor I (unitary-frame measure mass d),
while p.19 infers K = I/d and Eqs.(93)–(98) use the Bell density d |U^T><U^T|.
Changed: the reference measure is a probability measure and the frame integral is
I tensor I / d; the resource and contraction of Eq.(98) are unchanged.
Why: partial trace of Eq.(84) gives K = mu(Omega) I/d for a unitary family.
Dividing the Eq.(83) measure by d normalizes the Bell POVM in Eq.(98).
The shared state and Bell effects are computed from the frame; a normalized
measurable POVM on the same outcome space is a conclusion. The historical
classification assertion attributed to [28–30] is not claimed. -/
theorem ideal_teleportation
    {I W : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [MeasurableSpace W]
    (mu : Measure W) [IsProbabilityMeasure mu]
    (U : W → Matrix.unitaryGroup I ℂ)
    (hU : StronglyMeasurable (fun w => (U w : Matrix I I ℂ)))
    (hframe : Integrable (fun w => pureDensity
      (operatorKet (U w : Matrix I I ℂ))) mu)
    (htight : (∫ w, pureDensity (operatorKet (U w : Matrix I I ℂ)) ∂mu) =
      (Fintype.card I : ℂ)⁻¹ • (1 : Matrix (I × I) (I × I) ℂ)) :
    IsDensityMatrix (idealResource I) ∧
    (∃ D : Measurements.DensityPOVM (I × I) W,
      D.reference = mu ∧ D.density = (fun w => bellEffectDensity (U w : Matrix I I ℂ))) ∧
    ∀ (rho : Matrix I I ℂ), IsDensityMatrix rho → ∀ w,
      (U w : Matrix I I ℂ) *
        teleportRaw (idealResource I) (bellEffectDensity (U w : Matrix I I ℂ)) rho *
        (U w : Matrix I I ℂ)ᴴ = rho := by sorry

end QAlgorithms.Papers.Independent.Renew46.P20

end
