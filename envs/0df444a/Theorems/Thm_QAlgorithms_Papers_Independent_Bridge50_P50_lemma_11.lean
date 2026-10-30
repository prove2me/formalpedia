-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P50_lemma_11
-- name    : QAlgorithms.Papers.Independent.Bridge50.P50.lemma_11
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T09:28:38.526232+00:00
-- url     : https://prove2.me/theorems/aadc7cbb-7bb7-4066-bc87-f334e0304514
-- title:
--   Lemma 11: lemma 11
-- statement:
--   Let $E$ be a finite-dimensional real Hausdorff topological vector space and let $(\Theta_n)_{n\ge1}$ be decreasing compact subsets. If $\Theta_\infty=\bigcap_{n\ge1}\Theta_n$ is nonempty, then
--   $$
--   \bigcap_{n\ge1}\operatorname{conv}(\Theta_n)=\operatorname{conv}(\Theta_\infty).
--   $$
--   The convex hull is the ordinary finite convex hull. This is the compact-intersection identity used to pass to exactly peripheral states.
--
--   **Formalization Note** The sequence starts at index zero in Lean.
-- source:
--   Second-Order Asymptotics for the Classical Capacity of Image-Additive Quantum Channels, arXiv:1308.6503v3, PDF p. 13, Lemma 11

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P50

noncomputable section

open scoped Topology BigOperators ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Bridge50.P50

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted primitives; these names do not create local declarations.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat logTwo testingBeta normalCDF normalQuantile)

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble ensembleAverage)

open QAlgorithms.Papers.Independent.Information100.P69 (entropy)

open QAlgorithms.Papers.Independent.Dependency50.P35 (Dominates)

open QAlgorithms.Papers.Independent.Dependency50.P36 (pairInformationVariance)

open QAlgorithms (vnEntropy traceDistance minEigenvalue)

attribute [local instance] QAlgorithms.Papers.Independent.Bridge50.P50.matrixBorelMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Bridge50.P50.matrixBorelSpace

/-- Lemma 11, PDF pp.13,25: ordinary finite convex hull commutes with nested compact
intersection in a finite-dimensional real Hausdorff topological vector space.
Source Theta_1 is indexed by 0 here. -/
theorem lemma_11 {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] [FiniteDimensional ℝ E]
    (Theta : ℕ → Set E) (hc : ∀ n, IsCompact (Theta n)) (hn : Antitone Theta)
    (hi : (⋂ n, Theta n).Nonempty) :
    (⋂ n, convexHull ℝ (Theta n)) = convexHull ℝ (⋂ n, Theta n) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P50

end
