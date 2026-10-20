-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P35_conditional_order_antitone
-- name    : QAlgorithms.Papers.Independent.Dependency50.P35.conditional_order_antitone
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:02:03.040381+00:00
-- url     : https://prove2.me/theorems/b7b09f18-92d9-471a-b9cf-1c68d34d8947
-- title:
--   Conditional entropy is nonincreasing in its order
-- statement:
--   Let $\rho_{AB}\ge0$ have trace in $(0,1]$. For positive real orders $\alpha\le\beta$, with neither order equal to one,
--
--   $$
--   \widetilde H_\beta(A|B)_\rho\le\widetilde H_\alpha(A|B)_\rho.
--   $$
--
--   The comparison-state set $S_B$ is identical at every order, and the comparison includes orders straddling one. This is the conditional monotonicity announced in the introduction, interpreted through Theorem 7 and Definition 4.
-- source:
--   On quantum Renyi entropies: a new generalization and some properties, arXiv:1306.3142v4, PDF p. 2, Conditional entropy is nonincreasing in its order

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Dependency50.P35

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the accepted matrix type and positive-operator Schatten expression.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat schatten)

open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)

/-- PDF p.2, monotonicity bullet, with its precise order domain from pp.10–11. -/
theorem conditional_order_antitone {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (a b : ℝ)
    (ha : 0 < a ∧ a ≠ 1) (hb : 0 < b ∧ b ≠ 1) (hab : a ≤ b)
    (rho : Mat (A × B)) (hr : Substate rho) : conditionalRenyi b rho ≤ conditionalRenyi a rho := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P35

end
