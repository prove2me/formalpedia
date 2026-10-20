-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P35_conditional_distance
-- name    : QAlgorithms.Papers.Independent.Dependency50.P35.conditional_distance
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:59:48.030234+00:00
-- url     : https://prove2.me/theorems/08bc9cb6-c1da-42f1-8616-27b9baeadee3
-- title:
--   Conditional distance-to-maximal-entropy representation
-- statement:
--   For $\alpha\in(0,1)\cup(1,\infty)$ and $\rho_{AB}\ge0$ with trace in $(0,1]$, put $\rho_A=\operatorname{Tr}_B\rho_{AB}$, $d_A=\operatorname{rank}\rho_A$, and $\pi_A=P_{\rho_A}/d_A$, the maximally mixed state on its support. Then
--
--   $$
--   \widetilde H_\alpha(A|B)_\rho=\log_2d_A-\inf_{\sigma_B\in S_B}\widetilde D_\alpha(\rho_{AB}\|\pi_A\otimes\sigma_B).
--   $$
--
--   The optimization set $S_B$ is the nonzero subnormalized state set from Definition 4. This expresses conditional entropy as distance from a state maximally mixed on the actual $A$ support.
-- source:
--   On quantum Renyi entropies: a new generalization and some properties, arXiv:1306.3142v4, PDF p. 11, Conditional distance-to-maximal-entropy representation

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Dependency50.P35

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the accepted matrix type and positive-operator Schatten expression.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat schatten)

open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)

/-- PDF p.11: conditional distance to a maximally mixed support state. -/
theorem conditional_distance {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (a : ℝ) (ha : 0 < a ∧ a ≠ 1)
    (rho : Mat (A × B)) (hr : Substate rho) :
    conditionalRenyi a rho = (Real.logb 2 (supportRank (leftMarginal rho) : ℝ) : EReal) -
      sInf {v : EReal | ∃ sigma : Mat B, Substate sigma ∧
        v = divergence a rho (Matrix.kronecker (supportMixed (leftMarginal rho)) sigma)} := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P35

end
