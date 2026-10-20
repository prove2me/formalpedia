-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P35_dataProcessing_and_jointConvexity
-- name    : QAlgorithms.Papers.Independent.Dependency50.P35.dataProcessing_and_jointConvexity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:55:53.412933+00:00
-- url     : https://prove2.me/theorems/0168da64-0979-498c-b56a-bda7be89ccc1
-- title:
--   Theorem 6 (Data-Processing)
-- statement:
--   Fix $1<\alpha\le2$. For arbitrary finite input and output dimensions, any $\rho,\sigma\ge0$ with $\rho\ne0$, and every completely positive trace-preserving map $\mathcal E$,
--
--   $$
--   \widetilde D_\alpha(\mathcal E(\rho)\|\mathcal E(\sigma))\le\widetilde D_\alpha(\rho\|\sigma).
--   $$
--
--   Moreover, $(\rho,\sigma)\mapsto2^{(\alpha-1)\widetilde D_\alpha(\rho\|\sigma)}$ is jointly convex on pairs of normalized states. Infinite values are retained through support guards. This states both conclusions in the range proved in this paper; the normalized convexity domain follows footnote 46.
-- source:
--   On quantum Renyi entropies: a new generalization and some properties, arXiv:1306.3142v4, PDF p. 9, Theorem 6 (Data-Processing)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Dependency50.P35

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the accepted matrix type and positive-operator Schatten expression.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat schatten)

open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)

/-- PDF p.9, Theorem 6: the paper's proved range (1,2], and normalized-pair
joint convexity as specified in footnote 46 (PDF p.26). -/
theorem dataProcessing_and_jointConvexity {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (a : ℝ) (ha : 1 < a ∧ a ≤ 2) :
    (∀ (rho sigma : Mat I), rho.PosSemidef → sigma.PosSemidef → rho ≠ 0 →
      ∀ E : Superop I J, IsChannel E → divergence a (E rho) (E sigma) ≤ divergence a rho sigma) ∧
    NormalizedJointConvex (exponential (I := I) a) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P35

end
