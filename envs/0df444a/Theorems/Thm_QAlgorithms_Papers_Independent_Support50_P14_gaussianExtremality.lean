-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P14_gaussianExtremality
-- name    : QAlgorithms.Papers.Independent.Support50.P14.gaussianExtremality
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:26:39.452728+00:00
-- url     : https://prove2.me/theorems/ca5fd9e5-2c8f-42c3-a73d-a20e9d02eb0f
-- title:
--   Lemma 1, (2): general Gaussian extremality (original seed)
-- statement:
--   Let $M\ge1$ be the number of parties, and let $f$ be a compatible real-valued family on normalized density operators on all finite collections of full oscillator modes, with arbitrary ownership and tensor regrouping. Suppose $f$ is continuous in trace norm, invariant under independent local bounded unitaries, strongly superadditive, and additive on product states. If $\rho$ has finite oscillator energy, first moments $d$, and symmetric full anticommutator covariance $\Gamma$, there exists a normalized Gaussian density $\rho_G$ with those same moments, and
--
--   $$f(\rho_G)\le f(\rho).$$
--
--   The Gaussian characteristic function is $\chi_G(\xi)=\exp(i\xi\cdot d-\xi^T\Gamma\xi/4)$, with vacuum covariance $I$. This is the general extremality principle used by the applications.
-- source:
--   Extremality of Gaussian quantum states, arXiv:quant-ph/0509154v1, PDF p. 1, Lemma 1, (2): general Gaussian extremality (original seed)

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

/-- Lemma 1, PDF pp.1--2, (2). Full trace-norm continuity and strong
super-additivity INCLUDING product equality imply Gaussian extremality.
Existence of the actual Gaussian counterpart is a conclusion. -/
theorem gaussianExtremality {M : ℕ} (hM : 0 < M) (f : MultipartiteOscillatorFunctional M)
    (hcont : OscillatorTraceContinuous none f) (hssa : StronglySuperadditive none f)
    (hlocal : LocallyInvariant none f)
    {I : Type} [Fintype I] (owner : I → Fin M) (howner : Function.Surjective owner)
    (rho : State (Occupation I)) (d : InterleavedQuadrature I → ℝ) (gamma : OscillatorCovariance I)
    (hmoments : CompleteMoments rho.coefficients d gamma) :
    ∃ rhoG : State (Occupation I), GaussianAt rhoG.coefficients d gamma ∧
      f I owner rhoG.coefficients ≤ f I owner rho.coefficients := by sorry

end QAlgorithms.Papers.Independent.Support50.P14

end
