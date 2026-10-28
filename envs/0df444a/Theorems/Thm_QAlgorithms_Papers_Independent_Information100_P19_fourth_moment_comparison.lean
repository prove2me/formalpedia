-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P19_fourth_moment_comparison
-- name    : QAlgorithms.Papers.Independent.Information100.P19.fourth_moment_comparison
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T10:02:52.277858+00:00
-- url     : https://prove2.me/theorems/8f7577f7-118f-4d71-bb35-0e6bb6778284
-- title:
--   Proposition 6.3
-- statement:
--   For every PSD bipartite operator $X$, in arbitrary positive finite local dimensions,
--   $$r_2(X)\ge p_4(X^{\Gamma_B}),\qquad
--   \operatorname{Tr}_{(14)(23),(12)(34)}X-\operatorname{Tr}_{(1234),(1432)}X\ge0.$$
--   The corresponding tensor coefficient vector belongs to $I_4^{\rm sep}$. This inequality holds even on the full bipartite PSD cone and requires neither separability nor trace normalization.
--
--   Here $R(X)_{ik,jl}=X_{ij,kl}$ is realignment, $r_k(X)=\operatorname{Tr}[(R(X)R(X)^*)^k]$, and all traces are ordinary unnormalized matrix traces. We write $t=\operatorname{Tr}X$, $X_A=\operatorname{Tr}_B X$, $X_B=\operatorname{Tr}_A X$, $\widetilde X=tX-X_A\otimes X_B$, $\widetilde r_k=r_k(\widetilde X)$, and $G=(t^2-\operatorname{Tr}X_A^2)(t^2-\operatorname{Tr}X_B^2)$. The notation $q_k$ means $\operatorname{Tr}[(X^{\Gamma_B})^k]$, where $\Gamma_B$ transposes the B factor.
-- source:
--   Optimal entanglement criteria from trace invariants, arXiv:2609.29471v1, PDF p. 40, Proposition 6.3

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P19

/-- Proposition 6.3; arXiv:2609.29471v1, PDF pp.40, 41. -/
theorem fourth_moment_comparison  :
    (∀ a b, 0<a → 0<b → ∀ X : Bip a b, X.PosSemidef →
      powerTrace (transposeB X) 4 ≤ rMoment X 2 ∧
      0 ≤ (tensorTrace (alphaPerm 2,betaPerm 2) X).re -
        (tensorTrace (cycle4,cycle4⁻¹) X).re) ∧
    tensorBasis (alphaPerm 2,betaPerm 2)-tensorBasis (cycle4,cycle4⁻¹) ∈ sepCone 4 := by sorry

end QAlgorithms.Papers.Independent.Information100.P19

end
