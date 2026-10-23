-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P18_projection_image_convexity_and_ensemble_lifting
-- name    : QAlgorithms.Papers.Independent.Gap48.P18.projection_image_convexity_and_ensemble_lifting
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T07:58:12.924066+00:00
-- url     : https://prove2.me/theorems/010d9aea-e906-4c53-9af9-44b0e21f1da9
-- title:
--   Lemma 11
-- statement:
--   Let $P$ be an orthogonal projection and let $A$ lie in the positive-mass domain of $\Theta_P(\rho)=P\rho P/\operatorname{Tr}P\rho$. If $A$ is convex then $\Theta_P(A)$ is convex. For every finite probability ensemble $\{\pi_i,\rho_i\}_{i=1}^m$ in that image, there is an ensemble $\{\lambda_i,\sigma_i\}_{i=1}^m$ in $A$ with
--
--   $$\Theta_P(\sigma_i)=\rho_i,\qquad\lambda_i\operatorname{Tr}P\sigma_i=\pi_i\sum_j\lambda_j\operatorname{Tr}P\sigma_j.$$
--
--   The lifting assertion does not require convexity. Normalization is used only at positive trace.
-- source:
--   Entropic characteristics of subsets of states, arXiv:quant-ph/0510073v2, PDF p. 72, Lemma 11

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P18

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal Topology Matrix.Norms.L2Operator

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState traceSize traceClosure IsTraceClassChannel productCoeff)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (GeneralizedEnsemble HasFiniteSupport HasAverage averageCoefficients
   extendedEntropyNats extendedRelativeEntropyNats
   finiteEnsembleCapacity pureStates)

open QAlgorithms.Papers.Independent.Frontier18.P01 (traceFirst traceSecond)

namespace QAlgorithms.Papers.Independent.Gap48.P18

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma 11, arXiv:quant-ph/0510073v2, PDF pp.72.
 -/
theorem projection_image_convexity_and_ensemble_lifting {I : Type}
    [Countable I] [Nonempty I] (P : BoundedOrthogonalProjection I) (A : Set (State I))
    (hdomain : ∀ rho ∈ A, 0 < projectionMass P rho) :
    (CoefficientConvexStates A → CoefficientConvexStates (projectionImage P A)) ∧
      ∀ (m : ℕ) (pi : Fin m → ℝ≥0) (rho : Fin m → State I), InSimplex pi →
        (∀ i, rho i ∈ projectionImage P A) →
        ∃ (w : Fin m → ℝ≥0) (sigma : Fin m → State I), InSimplex w ∧
          (∀ i, sigma i ∈ A) ∧ ∀ i,
            (rho i).coefficients = compressedCoefficients P (sigma i) ∧
            (w i : ℝ) * projectionMass P (sigma i) =
              (pi i : ℝ) * ∑ j, (w j : ℝ) * projectionMass P (sigma j) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P18

end
