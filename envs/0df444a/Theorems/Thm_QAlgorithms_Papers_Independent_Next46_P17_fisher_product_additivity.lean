-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P17_fisher_product_additivity
-- name    : QAlgorithms.Papers.Independent.Next46.P17.fisher_product_additivity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:20:07.942996+00:00
-- url     : https://prove2.me/theorems/cda013ad-05d7-4bb9-ba30-4f1d5d5785c4
-- title:
--   Additivity on independent parameterized quantum states
-- statement:
--   Let $\rho_{A,\theta}$ and $\rho_{B,\theta}$ be normalized density operators on two separable Hilbert spaces, which may have different dimensions, and fix $u\in\mathbb R$. For each factor assume its relative entropy from the state at $u$ is finite near $u$, differentiable on a neighborhood, and has differentiable first derivative at $u$. All relative entropies use natural logarithms. For the product family, independence holds at every parameter. Then
--
--   $$
--   J(\rho_A\otimes\rho_B;u)=J(\rho_A;u)+J(\rho_B;u).
--   $$
--
--   Thus independent quantum systems contribute additively to divergence-based Fisher information.
-- source:
--   The entropy power inequality for quantum systems, arXiv:1205.3409v2, PDF p. 10, Lemma IV.3

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P17

noncomputable section

open Filter MeasureTheory

open scoped ENNReal BigOperators Topology

namespace QAlgorithms.Papers.Independent.Next46.P17

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsTraceClass IsTraceClassChannel productCoeff tensorApply)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (extendedEntropyNats extendedRelativeEntropyNats)

open QAlgorithms.Papers.Independent.Claimed50.P19 (productWeyl FiniteMeanEnergy PhysicalCovariance Cov FockIndex covarianceCharacteristicValue)

open QAlgorithms.Papers.Independent.Frontier30.P08 (interleavedSymplecticForm)

/-- PDF p.10, Lemma IV.3, (72). The two separable factors may have different
Hilbert dimensions. Independence holds for every value of the shared parameter. -/
theorem fisher_product_additivity {I J : Type} [Countable I] [Countable J]
    (rhoA : ℝ → State I) (rhoB : ℝ → State J) (base : ℝ)
    (hA : FisherRegular (fun theta => (rhoA theta).coefficients) base)
    (hB : FisherRegular (fun theta => (rhoB theta).coefficients) base) :
    fisher (fun theta => productCoeff (rhoA theta).coefficients
        (rhoB theta).coefficients) base =
      fisher (fun theta => (rhoA theta).coefficients) base +
      fisher (fun theta => (rhoB theta).coefficients) base := by sorry

end QAlgorithms.Papers.Independent.Next46.P17

end
