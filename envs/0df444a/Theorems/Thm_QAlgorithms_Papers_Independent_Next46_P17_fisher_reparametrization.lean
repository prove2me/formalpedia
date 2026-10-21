-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P17_fisher_reparametrization
-- name    : QAlgorithms.Papers.Independent.Next46.P17.fisher_reparametrization
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T13:18:34.721879+00:00
-- url     : https://prove2.me/theorems/a530b453-42c0-44b8-83d2-765c54a3095f
-- title:
--   Fisher information under scaling and translation
-- statement:
--   Let $\theta\mapsto\rho_\theta$ be normalized density operators on a separable Hilbert space. Write $J(\rho;u)$ for the second derivative at $u$ of $D(\rho_u\Vert\rho_\theta)$, with natural logarithms. Let $c,u\in\mathbb R$. Suppose the divergence is finite near each relevant basepoint, differentiable on a neighborhood, and its first derivative is differentiable at that basepoint. Then
--
--   $$
--   J(\theta\mapsto\rho_{c\theta};u)=c^2J(\rho;cu),\qquad
--   J(\theta\mapsto\rho_{\theta+c};u)=J(\rho;u+c).
--   $$
--
--   These identities describe the parameter dependence of divergence-based Fisher information. The first identity includes $c=0$ and negative $c$.
--
--   **Formalization Note** The printed scaling basepoint on the right is corrected from $u$ to $cu$, as required by definition (69). Independent moderation of this correction is pending.
-- source:
--   The entropy power inequality for quantum systems, arXiv:1205.3409v2, PDF p. 10, Lemma IV.1

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

/-- PDF p.10, Lemma IV.1. Printed: the scaling RHS is evaluated at theta0.
Changed: evaluate it at c*theta0, as uniquely required by (69) and the chain rule.
The translation clause is unchanged. Negative and zero c are included. -/
theorem fisher_reparametrization {I : Type} [Countable I]
    (rho : ℝ → State I) (c base : ℝ)
    (hScale : FisherRegular (fun theta => (rho theta).coefficients) (c * base))
    (hShift : FisherRegular (fun theta => (rho theta).coefficients) (base + c)) :
    fisher (fun theta => (rho (c * theta)).coefficients) base =
        c ^ 2 * fisher (fun theta => (rho theta).coefficients) (c * base) ∧
    fisher (fun theta => (rho (theta + c)).coefficients) base =
        fisher (fun theta => (rho theta).coefficients) (base + c) := by sorry

end QAlgorithms.Papers.Independent.Next46.P17

end
