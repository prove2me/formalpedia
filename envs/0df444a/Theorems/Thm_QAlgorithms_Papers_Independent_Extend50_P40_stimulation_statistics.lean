-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P40_stimulation_statistics
-- name    : QAlgorithms.Papers.Independent.Extend50.P40.stimulation_statistics
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:20:53.768994+00:00
-- url     : https://prove2.me/theorems/517e0953-b429-4e41-9bac-819e703acf0f
-- title:
--   §V.B.2–3 Eqs.(91)–(96): stimulation statistics and normalization
-- statement:
--   Let $N\ge1$ input photons occupy one polarization, let $A$ initially excited identical Lambda atoms have equal real coupling $g$, and let $t\ge0$ be the interaction time. Use the full excitation-preserving Hamiltonian (93), including reabsorption. For $k\le A$ emitted photons and $0\le l\le k$, its unnormalized probabilities obey
--
--   $$
--   P_{k,l}=\binom{N+l}{N}P_{k,0},\qquad P_k=\binom{N+k+1}{N+1}P_{k,0}.
--   $$
--
--   The evolved vector is normalized. If P_k>0, the conditional mean number emitted in the initial polarization is k(N+1)/(N+2). At zero success only the unnormalized identities are asserted; k=0 gives conditional mean zero. The exact finite conserved sector is not a photon cutoff.
-- source:
--   Quantum cloning, arXiv:quant-ph/0511088v1, PDF p. 24, §V.B.2–3 Eqs.(91)–(96): stimulation statistics and normalization

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

/-- V.B.2–3, PDF p.24 Eqs.(91)–(96): exact full-evolution relative weights,
normalization and conditional mean. No conditional value is assigned to a zero
success event. The finite A-atom sector permits only k≤A. -/
theorem stimulation_statistics (N A k : ℕ) (hN : 1 ≤ N) (hk : k ≤ A) (g t : ℝ) (ht : 0 ≤ t) :
    ‖emissionState N A g t‖ = 1 ∧
    (∀ l : ℕ, l ≤ k → emissionProbability N A k l g t =
      (Nat.choose (N + l) N : ℝ) * emissionProbability N A k 0 g t) ∧
    emissionSuccess N A k g t =
      (Nat.choose (N + k + 1) (N + 1) : ℝ) * emissionProbability N A k 0 g t ∧
    (0 < emissionSuccess N A k g t →
      (∑ l ∈ Finset.range (k + 1), (l : ℝ) * emissionProbability N A k l g t) /
        emissionSuccess N A k g t = (k : ℝ) * (N + 1) / (N + 2)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P40

end
