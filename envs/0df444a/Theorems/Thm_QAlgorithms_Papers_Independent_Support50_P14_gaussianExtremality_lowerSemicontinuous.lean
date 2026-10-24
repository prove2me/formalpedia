-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P14_gaussianExtremality_lowerSemicontinuous
-- name    : QAlgorithms.Papers.Independent.Support50.P14.gaussianExtremality_lowerSemicontinuous
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:27:41.009393+00:00
-- url     : https://prove2.me/theorems/8564f0ee-d3c6-425d-a8fe-3f76c523991d
-- title:
--   Lemma 1, unnumbered lower-semicontinuity refinement
-- statement:
--   Let $f$ be a compatible real-valued family on $M\ge1$ parties, invariant under independent local bounded unitaries and mode regrouping, strongly superadditive, and additive on products. Its domain may be all normalized densities, or the compatible sublevels of mean photon number $\operatorname{Tr}(\rho\sum_j a_j^\dagger a_j)\le e n$ on $n$ modes, for a fixed $e\ge0$. Assume lower semicontinuity in the relative trace-norm topology on each such domain. For every density $\rho$ in the domain with finite complete first and second moments $(d,\Gamma)$, a Gaussian density $\rho_G$ with the same moments belongs to the domain and satisfies
--
--   $$f(\rho_G)\le f(\rho).$$
--
--   This gives the stated weakening of continuity, including construction-compatible compact oscillator-energy sublevels. Domain membership is required for every state used in an algebraic clause.
-- source:
--   Extremality of Gaussian quantum states, arXiv:quant-ph/0509154v1, PDF p. 2, Lemma 1, unnumbered lower-semicontinuity refinement

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

/-- Lemma 1 refinement, PDF p.2: lower semicontinuity suffices, on the full
state space (cap=none) or compatible finite oscillator-energy sublevels
(cap=some e, e>=0). No arbitrary compact set is assumed construction-invariant. -/
theorem gaussianExtremality_lowerSemicontinuous {M : ℕ} (hM : 0 < M)
    (cap : Option ℝ) (hcap : ∀ e, cap = some e → 0 ≤ e) (f : MultipartiteOscillatorFunctional M)
    (hlsc : TraceLowerSemicontinuous cap f) (hssa : StronglySuperadditive cap f)
    (hlocal : LocallyInvariant cap f)
    {I : Type} [Fintype I] (owner : I → Fin M) (howner : Function.Surjective owner)
    (rho : State (Occupation I)) (hdomain : InDomain cap rho.coefficients)
    (d : InterleavedQuadrature I → ℝ) (gamma : OscillatorCovariance I)
    (hmoments : CompleteMoments rho.coefficients d gamma) :
    ∃ rhoG : State (Occupation I), GaussianAt rhoG.coefficients d gamma ∧
      InDomain cap rhoG.coefficients ∧
      f I owner rhoG.coefficients ≤ f I owner rho.coefficients := by sorry

end QAlgorithms.Papers.Independent.Support50.P14

end
