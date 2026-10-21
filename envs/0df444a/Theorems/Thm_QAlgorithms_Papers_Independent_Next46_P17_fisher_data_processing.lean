-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P17_fisher_data_processing
-- name    : QAlgorithms.Papers.Independent.Next46.P17.fisher_data_processing
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:20:56.490847+00:00
-- url     : https://prove2.me/theorems/63cc0a14-9d52-49fc-b480-6cab11dcb266
-- title:
--   Data processing of divergence-based Fisher information
-- statement:
--   Let $\mathcal E$ be a fixed completely positive trace-preserving linear map between the full trace-class operator spaces of separable Hilbert spaces. Let $\rho_\theta$ be normalized density operators and fix $u\in\mathbb R$. Assume both $D(\rho_u\Vert\rho_\theta)$ and $D(\mathcal E(\rho_u)\Vert\mathcal E(\rho_\theta))$ are finite near $u$, differentiable on a neighborhood, and have differentiable first derivatives at $u$. Then, using natural logarithms,
--
--   $$
--   J(\mathcal E\circ\rho;u)\leq J(\rho;u).
--   $$
--
--   A fixed channel cannot increase this Fisher information on its actual derivative domain.
--
--   **Formalization Note** Output differentiability is explicit under the standing smoothness convention. The proof's scalar domination argument alone does not establish it.
-- source:
--   The entropy power inequality for quantum systems, arXiv:1205.3409v2, PDF p. 10, Theorem IV.4

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

/-- PDF p.10, Theorem IV.4. The channel is fixed throughout the family.
The actual twice-differentiability of the output divergence is explicit under
the standing p.5 smoothness convention: scalar domination alone does not imply it. -/
theorem fisher_data_processing {I J : Type} [Countable I] [Countable J]
    (Phi : Matrix I I ℂ → Matrix J J ℂ) (hPhi : IsTraceClassChannel Phi)
    (rho : ℝ → State I) (base : ℝ)
    (hInput : FisherRegular (fun theta => (rho theta).coefficients) base)
    (hOutput : FisherRegular (fun theta => Phi (rho theta).coefficients) base) :
    fisher (fun theta => Phi (rho theta).coefficients) base ≤
      fisher (fun theta => (rho theta).coefficients) base := by sorry

end QAlgorithms.Papers.Independent.Next46.P17

end
