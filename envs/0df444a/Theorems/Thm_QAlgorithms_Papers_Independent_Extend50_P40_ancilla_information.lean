-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P40_ancilla_information
-- name    : QAlgorithms.Papers.Independent.Extend50.P40.ancilla_information
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:19:28.444109+00:00
-- url     : https://prove2.me/theorems/999d8da0-8292-420b-9c1d-04472a8a9bdb
-- title:
--   §IV.B.2 Eqs.(83)–(84): ancilla attack and 14.6% raw-rate threshold
-- statement:
--   For $0\le\theta\le\pi/2$, retain both Eve qubits of the ancilla phase cloner. The specified Bell decoder gives exactly the error-flag factorization (84). Reading the flag in Z and the other qubit in X yields, with uniform raw bits,
--
--   $$
--   I(A:E)=I(B:E)=1-H((1+\sin\theta)/2).
--   $$
--
--   The maximal binary discrimination success on Eve’s actual two-qubit states is (1+sinθ)/2 and is attained. The displayed raw rate is positive exactly when θ<π/4, equivalently D<(1−1/√2)/2. The deterministic flag explains the improvement over the economical reverse-reconciliation attack; no preprocessing-capacity claim is made.
-- source:
--   Quantum cloning, arXiv:quant-ph/0511088v1, PDF p. 22, §IV.B.2 Eqs.(83)–(84): ancilla attack and 14.6% raw-rate threshold

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

/-- IV.B.2, PDF pp.21–22 Eqs.(83)–(84): Eve retains BOTH qubits, reads the
error flag, and achieves equal Alice/Eve and Bob/Eve informations. The threshold
is for the displayed raw information rate without noisy preprocessing. -/
theorem ancilla_information (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ Real.pi / 2) :
    bellDecoderᴴ * bellDecoder = 1 ∧
    (∀ bit, decodedAttack theta bit = flagFactorization theta bit) ∧
    (∀ bit, IsDensityMatrix (eveGivenAlice theta bit)) ∧
    (classicalMutualInformation (fun a e => ∑ b, ancillaLaw theta a b e) =
      binaryInformation ((1 + Real.sin theta) / 2)) ∧
    (classicalMutualInformation (fun b e => ∑ a, ancillaLaw theta a b e) =
      binaryInformation ((1 + Real.sin theta) / 2)) ∧
    (∀ E : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ, IsEffect E →
      ((E * eveGivenAlice theta false).trace.re +
        ((1 - E) * eveGivenAlice theta true).trace.re) / 2 ≤ (1 + Real.sin theta) / 2) ∧
    (∃ E : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ, IsEffect E ∧
      ((E * eveGivenAlice theta false).trace.re +
        ((1 - E) * eveGivenAlice theta true).trace.re) / 2 = (1 + Real.sin theta) / 2) ∧
    (0 < rawRate (binaryInformation ((1 + Real.cos theta) / 2))
      (binaryInformation ((1 + Real.sin theta) / 2)) (binaryInformation ((1 + Real.sin theta) / 2)) ↔
      theta < Real.pi / 4) ∧
    ((1 - Real.cos theta) / 2 < (1 - 1 / Real.sqrt 2) / 2 ↔ theta < Real.pi / 4) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P40

end
