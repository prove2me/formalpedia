-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P35_conditional_dataProcessing
-- name    : QAlgorithms.Papers.Independent.Dependency50.P35.conditional_dataProcessing
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:00:37.636216+00:00
-- url     : https://prove2.me/theorems/9e4eabd9-9fc9-44fb-8428-587a58db5c11
-- title:
--   Conditional data-processing inequality
-- statement:
--   Let $\alpha\in[1/2,1)\cup(1,\infty)$, let $\rho_{AB}\ge0$ have trace in $(0,1]$, and let $\mathcal E:B\to B'$ be a completely positive trace-preserving map. Define $\tau_{AB'}=(\mathrm{id}_A\otimes\mathcal E)(\rho_{AB})$. Then
--
--   $$
--   \widetilde H_\alpha(A|B)_\rho\le\widetilde H_\alpha(A|B')_\tau.
--   $$
--
--   The conditional entropies optimize over all nonzero subnormalized comparison states. This full-range conditional data-processing consequence uses the divergence result credited by the source to Frank and Lieb [12].
-- source:
--   On quantum Renyi entropies: a new generalization and some properties, arXiv:1306.3142v4, PDF p. 11, Conditional data-processing inequality

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Dependency50.P35

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the accepted matrix type and positive-operator Schatten expression.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat schatten)

open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)

/-- PDF pp.11–12: the full conditional DPI range, credited there to Frank–Lieb [12].
The output is constructed by applying the channel to the B register. -/
theorem conditional_dataProcessing {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (a : ℝ) (ha : (1/2 : ℝ) ≤ a ∧ a ≠ 1) (rho : Mat (A × B)) (hr : Substate rho)
    (E : Superop B C) (hE : IsChannel E) :
    conditionalRenyi a rho ≤ conditionalRenyi a (idTensorSuperop E rho) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P35

end
