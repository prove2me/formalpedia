-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P33_amplitude_photon_mean
-- name    : QAlgorithms.Papers.Independent.Advance50.P33.amplitude_photon_mean
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:36:32.108781+00:00
-- url     : https://prove2.me/theorems/ea2ce034-35b6-4fd6-b38c-e4bd278d5404
-- title:
--   A larger cat amplitude has a larger finite photon mean
-- statement:
--   Let $0<A<A_{\rm new}$ be positive real cat amplitudes and fix the same branch $b\in\{0,1\}$, with $b=0$ odd and $b=1$ even. Alice prepares the corresponding honest-form encoding, Bob recombines the modes correctly in the ideal balanced interferometer, and counts photons in the cat output. Both cat vectors are normalized and both mean-photon series are finite. Writing
--   $$
--   \bar n_b(A)=\sum_{n=0}^{\infty} n\,|\langle n|c_b(A)\rangle|^2,
--   $$
--   one has
--   $$
--   \bar n_b(A)<\bar n_b(A_{\rm new}).
--   $$
--   Since the entangled-state amplitude and cat amplitude differ by the same positive factor $\sqrt2$, this also gives the source's ordering for committed amplitudes. The comparison concerns the same parity branch; it is not a general state-certification or binding theorem.
-- source:
--   Quantum bit commitment under Gaussian constraints, arXiv:1105.2140v2, PDF p. 8, V: a larger committed cat amplitude has a larger mean photon number

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P33

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P33

open Filter

open scoped BigOperators Topology

open QAlgorithms.Papers.Independent.Dependency50.P39
  (Fock FockOperator BipartiteFock fockKet bipartiteKet coherentKet
   coherentCoefficient CoherentRealized displacement displacementMatrix
   DisplacementRealized HasFockMatrix operatorOfMatrix IsDensity IsTraceClass
   nuclearTraceNorm fockTrace)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.8: larger positive real cat amplitude gives a strictly larger FINITE
mean photon number in the same parity branch. This is only the concrete
observable comparison, not certification of an arbitrary state or a security test. -/
theorem amplitude_photon_mean (A Anew : ℝ) (hA : 0 < A) (hNew : A < Anew) (b : Bool) :
    CoherentRealized ∧ ‖cat (A : ℂ) b‖ = 1 ∧ ‖cat (Anew : ℂ) b‖ = 1 ∧
    Summable (fun n : ℕ => (n : ℝ) * ‖cat (A : ℂ) b n‖ ^ 2) ∧
    Summable (fun n : ℕ => (n : ℝ) * ‖cat (Anew : ℂ) b n‖ ^ 2) ∧
    catPhotonMean (A : ℂ) b < catPhotonMean (Anew : ℂ) b := by sorry

end QAlgorithms.Papers.Independent.Advance50.P33

end
