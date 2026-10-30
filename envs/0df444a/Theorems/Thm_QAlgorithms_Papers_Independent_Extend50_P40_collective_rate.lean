-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P40_collective_rate
-- name    : QAlgorithms.Papers.Independent.Extend50.P40.collective_rate
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:20:05.273945+00:00
-- url     : https://prove2.me/theorems/2a62f6ba-c7e0-4f21-ae00-2cec346e0864
-- title:
--   §IV.C Eqs.(85)–(86): BB84 phase-cloner collective-attack rate
-- statement:
--   For the ancilla phase-cloner attack, let $D=(1-\cos\theta)/2$ with $0\le\theta\le\pi/2$. Compute both conditional Eve ensembles from the actual interaction, and let $\chi$ denote their binary Holevo quantities in bits. Then
--
--   $$
--   \chi(A:E)=\chi(B:E)=H(D),\qquad R=1-2H(D).
--   $$
--
--   There is a unique d_c in (0,1/2) with 1−2H(d_c)=0; on [0,1/2], R is positive exactly below d_c. This is the source’s collective-attack raw rate and its exact implicit threshold, not a rounded decimal or unrestricted secret-key capacity.
-- source:
--   Quantum cloning, arXiv:quant-ph/0511088v1, PDF p. 22, §IV.C Eqs.(85)–(86): BB84 phase-cloner collective-attack rate

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

/-- IV.C, PDF p.22 Eqs.(85)–(86): exact rate of this collective attack, with
its unique implicit critical error. No decimal 0.11 equality or capacity claim. -/
theorem collective_rate :
    (∀ theta ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      (∀ bit, IsDensityMatrix (eveGivenAlice theta bit) ∧ IsDensityMatrix (eveGivenBob theta bit)) ∧
      binaryHolevo (eveGivenAlice theta false) (eveGivenAlice theta true) = binEntropy2 ((1 - Real.cos theta) / 2) ∧
      binaryHolevo (eveGivenBob theta false) (eveGivenBob theta true) = binEntropy2 ((1 - Real.cos theta) / 2) ∧
      collectiveRate theta = 1 - 2 * binEntropy2 ((1 - Real.cos theta) / 2)) ∧
    ∃ dc : ℝ, 0 < dc ∧ dc < 1 / 2 ∧ 1 - 2 * binEntropy2 dc = 0 ∧
      (∀ d ∈ Set.Icc (0 : ℝ) (1 / 2), 1 - 2 * binEntropy2 d = 0 ↔ d = dc) ∧
      (∀ d ∈ Set.Icc (0 : ℝ) (1 / 2), 0 < 1 - 2 * binEntropy2 d ↔ d < dc) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P40

end
