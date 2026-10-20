-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P35_more_conditioning
-- name    : QAlgorithms.Papers.Independent.Dependency50.P35.more_conditioning
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:01:21.109774+00:00
-- url     : https://prove2.me/theorems/6dc9866d-d8fb-4d87-bc7e-5d933bd1defb
-- title:
--   Conditioning on more systems reduces entropy
-- statement:
--   Let $\rho_{ABC}\ge0$ have trace in $(0,1]$, let $\rho_{AB}=\operatorname{Tr}_C\rho_{ABC}$, and take $\alpha\in[1/2,1)\cup(1,\infty)$. Then
--
--   $$
--   \widetilde H_\alpha(A|B)_{\rho_{AB}}\ge\widetilde H_\alpha(A|BC)_{\rho_{ABC}}.
--   $$
--
--   This is the source's explicit consequence that retaining additional conditioning systems cannot increase conditional entropy.
-- source:
--   On quantum Renyi entropies: a new generalization and some properties, arXiv:1306.3142v4, PDF p. 12, Conditioning on more systems reduces entropy

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Dependency50.P35

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the accepted matrix type and positive-operator Schatten expression.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat schatten)

open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)

/-- PDF p.12: discarding C cannot decrease A's conditional entropy. -/
theorem more_conditioning {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (a : ℝ) (ha : (1/2 : ℝ) ≤ a ∧ a ≠ 1)
    (rho : Mat (A × (B × C))) (hr : Substate rho) :
    conditionalRenyi a rho ≤ conditionalRenyi a (marginalAB rho) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P35

end
