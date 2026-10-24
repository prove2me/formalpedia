-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P14_multipartiteEntanglementMinimum
-- name    : QAlgorithms.Papers.Independent.Support50.P14.multipartiteEntanglementMinimum
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:31:48.463812+00:00
-- url     : https://prove2.me/theorems/2e2a2d5d-43f0-4602-91e6-1585875dd7c0
-- title:
--   Proposition 1: multipartite entanglement minimum
-- statement:
--   Consider $M\ge1$ parties, each holding an arbitrary positive finite number of full oscillator modes. Let $E$ be a compatible real-valued functional family that is continuous in trace norm, strongly superadditive with equality on product states, and invariant under independent local unitaries. In particular these are the properties required of the entanglement measure in Proposition 1; local-unitary invariance is part of that convention. If $\rho$ has finite complete moments and $\rho_G$ is any Gaussian density with the same symmetric covariance, then
--
--   $$E(\rho_G)\le E(\rho).$$
--
--   The first moments may differ. The statement displays the functional properties actually used by the proposition, so it applies to every entanglement measure satisfying its hypotheses without selecting one named measure.
-- source:
--   Extremality of Gaussian quantum states, arXiv:quant-ph/0509154v1, PDF p. 3, Proposition 1: multipartite entanglement minimum

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

/-- Proposition 1, PDF p.3: arbitrary finite nonempty mode groups at M parties.
The entanglement-measure convention is used through its local-unitary invariance;
the other requirements are trace continuity and strong super-additivity with
product equality. The conclusion is valid for every functional with these
properties, hence for every entanglement measure satisfying the stated axioms.
Only covariance is shared; d and dG are independent. -/
theorem multipartiteEntanglementMinimum {M : ℕ} (hM : 0 < M) (E : MultipartiteOscillatorFunctional M)
    (hcont : OscillatorTraceContinuous none E) (hssa : StronglySuperadditive none E)
    (hentanglementLocalInvariance : LocallyInvariant none E)
    {I : Type} [Fintype I] (owner : I → Fin M) (howner : Function.Surjective owner)
    (rho rhoG : State (Occupation I)) (d dG : InterleavedQuadrature I → ℝ) (gamma : OscillatorCovariance I)
    (hmoments : CompleteMoments rho.coefficients d gamma)
    (hgaussian : GaussianAt rhoG.coefficients dG gamma) :
    E I owner rhoG.coefficients ≤ E I owner rho.coefficients := by sorry

end QAlgorithms.Papers.Independent.Support50.P14

end
