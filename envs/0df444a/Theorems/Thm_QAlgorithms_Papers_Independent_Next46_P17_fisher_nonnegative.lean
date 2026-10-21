-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P17_fisher_nonnegative
-- name    : QAlgorithms.Papers.Independent.Next46.P17.fisher_nonnegative
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T13:19:25.980986+00:00
-- url     : https://prove2.me/theorems/2bb72953-dcae-49b3-a074-931776fc85e8
-- title:
--   Nonnegativity of divergence-based Fisher information
-- statement:
--   Let $\rho_\theta$ be a family of normalized density operators on a separable Hilbert space and $u\in\mathbb R$. Assume $f(\theta)=D(\rho_u\Vert\rho_\theta)$ is finite near $u$, differentiable there, and has a differentiable first derivative at $u$. The divergence uses natural logarithms. Then
--
--   $$
--   J(\rho;u):=f''(u)\geq0.
--   $$
--
--   This is positivity of the divergence-based Fisher information on its genuine finite derivative domain.
-- source:
--   The entropy power inequality for quantum systems, arXiv:1205.3409v2, PDF p. 10, Lemma IV.2

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

/-- PDF p.10, Lemma IV.2, with the finite derivative domain of pp.5,9. -/
theorem fisher_nonnegative {I : Type} [Countable I]
    (rho : ℝ → State I) (base : ℝ)
    (h : FisherRegular (fun theta => (rho theta).coefficients) base) :
    0 ≤ fisher (fun theta => (rho theta).coefficients) base := by sorry

end QAlgorithms.Papers.Independent.Next46.P17

end
