-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P35_chain_rule
-- name    : QAlgorithms.Papers.Independent.Dependency50.P35.chain_rule
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:03:12.187243+00:00
-- url     : https://prove2.me/theorems/c4525c10-4d33-4054-87b1-9aeca50b6da8
-- title:
--   Proposition 8 (Chain Rule)
-- statement:
--   Let $\alpha\in(0,1)\cup(1,\infty)$ and let $\rho_{ABC}\ge0$ have trace in $(0,1]$. Set $\rho_C=\operatorname{Tr}_{AB}\rho_{ABC}$ and $d_C=\operatorname{rank}\rho_C>0$. Then
--
--   $$
--   \widetilde H_\alpha(A|BC)_\rho\ge\widetilde H_\alpha(AC|B)_\rho-\log_2d_C.
--   $$
--
--   Both entropies use the same tripartite operator, with its tensor factors regrouped. The bound measures the cost of conditioning on $C$ by its support dimension, not its ambient dimension.
-- source:
--   On quantum Renyi entropies: a new generalization and some properties, arXiv:1306.3142v4, PDF p. 12, Proposition 8 (Chain Rule)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Dependency50.P35

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the accepted matrix type and positive-operator Schatten expression.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat schatten)

open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)

/-- PDF p.12, Proposition 8: rank of the actual C marginal and the same state
reordered as AC,B, at the full Definition 4 order range. -/
theorem chain_rule {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (a : ℝ) (ha : 0 < a ∧ a ≠ 1) (rho : Mat (A × (B × C))) (hr : Substate rho) :
    conditionalRenyi a (reorderACB rho) -
      (Real.logb 2 (supportRank (rightMarginal (rightMarginal rho)) : ℝ) : EReal) ≤
        conditionalRenyi a rho := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P35

end
