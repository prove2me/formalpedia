-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P35_conditional_optimizer
-- name    : QAlgorithms.Papers.Independent.Dependency50.P35.conditional_optimizer
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:58:36.507676+00:00
-- url     : https://prove2.me/theorems/10b7295d-f4f2-48ed-940e-e8534c30bb45
-- title:
--   Definition 4 aftermath: finite attained conditional optimum
-- statement:
--   Let $\alpha\in(0,1)\cup(1,\infty)$ and let $\rho_{AB}\ge0$ have trace in $(0,1]$. Define $\widetilde H_\alpha(A|B)_\rho=\sup_{\sigma_B\in S_B}-\widetilde D_\alpha(\rho_{AB}\|I_A\otimes\sigma_B)$, where $S_B$ consists of PSD operators with trace in $(0,1]$. Then this value is a finite real number and there exists a normalized optimizer $\sigma_B^*$ such that
--
--   $$
--   \widetilde H_\alpha(A|B)_\rho=-\widetilde D_\alpha(\rho_{AB}\|I_A\otimes\sigma_B^*),\quad
--   \alpha>1\Rightarrow\operatorname{supp}\rho_B\subseteq\operatorname{supp}\sigma_B^*,\quad
--   \alpha<1\Rightarrow\operatorname{supp}\sigma_B^*\subseteq\operatorname{supp}\rho_B.
--   $$
--
--   Here $\rho_B=\operatorname{Tr}_A\rho_{AB}$. This is existence of one optimizer with the stated support properties, without a compactness hypothesis.
-- source:
--   On quantum Renyi entropies: a new generalization and some properties, arXiv:1306.3142v4, PDF p. 11, Definition 4 aftermath

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Dependency50.P35

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the accepted matrix type and positive-operator Schatten expression.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat schatten)

open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)

/-- PDF p.11, Definition 4 aftermath: finite value and an attained normalized
optimizer with the stated direction of support inclusion. -/
theorem conditional_optimizer {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (a : ℝ) (ha : 0 < a ∧ a ≠ 1)
    (rho : Mat (A × B)) (hr : Substate rho) :
    ∃ h : ℝ, conditionalRenyi a rho = (h : EReal) ∧
      ∃ sigma : Mat B, Density sigma ∧
        -divergence a rho (Matrix.kronecker (1 : Mat A) sigma) = (h : EReal) ∧
        (1 < a → Dominates sigma (rightMarginal rho)) ∧
        (a < 1 → Dominates (rightMarginal rho) sigma) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P35

end
