-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P12_corollaryD_3
-- name    : QAlgorithms.Papers.Independent.Claimed50.P12.corollaryD_3
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T18:58:23.253981+00:00
-- url     : https://prove2.me/theorems/00379787-c9d6-4759-87d2-75700a6fce92
-- title:
--   Quantitative faithfulness of squashed entanglement
-- statement:
--   For every density operator $\rho_{AC}$ on nonzero finite-dimensional systems,
--
--   $$\inf_{\sigma\in\mathcal S_{A:C}}\Delta(\rho_{AC},\sigma)\le2\dim C\,\bigl(2\ln2\,E_{\rm sq}(\rho_{AC})\bigr)^{1/4}.$$
--
--   Here $\mathcal S_{A:C}$ is the set of separable density operators and $E_{\rm sq}$ takes its infimum over all finite-dimensional extensions. Zero squashed entanglement is included; no division by the entropy or positive-entropy hypothesis is introduced.
-- source:
--   Quantum conditional mutual information and approximate Markov chains, arXiv:1410.0664v3, PDF p. 28, Corollary D.3

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P12

noncomputable section

open Filter MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P12

open QAlgorithms.Papers.Independent.Information100.P32 (Op)

open QAlgorithms.Papers.Independent.Information100.P69 (CP matrixPower permute)

open QAlgorithms.Papers.Independent.Information100.P80 (OperatorLE groupedPower)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

/-- Corollary D.3, Eq.218 (PDF p.28): the fourth root includes the entropy.
Zero squashed entanglement is included, without using the proof's singular ceiling formula. -/
theorem corollaryD_3 {A C : Type*} [Fintype A] [Fintype C] [DecidableEq A] [DecidableEq C]
    [Nonempty A] [Nonempty C] (rho : Op (A × C)) (hrho : IsDensityMatrix rho) :
    separableDistance rho ≤ 2 * (Fintype.card C : ℝ) *
      (2 * Real.log 2 * squashedEntanglement rho) ^ (1 / (4 : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P12

end
