-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P19_discrete_separability_bounds
-- name    : QAlgorithms.Papers.Independent.Information100.P19.discrete_separability_bounds
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:59:27.387515+00:00
-- url     : https://prove2.me/theorems/c8b8142b-9431-43d2-8892-7f6b20d35d5f
-- title:
--   Proposition 5.12
-- statement:
--   Let $X$ be a nonzero unnormalized separable positive operator and $m\ge1$. With $t=\operatorname{Tr}X>0$, write $r(Y)$ for the first $m$ even realignment moments of $Y$. Then
--   $$\alpha(r(X/t))\le\|R(X)\|_1/t\le1.$$
--   When $G(X)>0$, also
--   $$\alpha(r(\widetilde X/\sqrt{G(X)}))\le\|R(\widetilde X)\|_1/\sqrt{G(X)}\le1.$$
--   The denominators have explicit positivity guards, and the inequalities are conclusions rather than assumptions.
--
--   Here $R(X)_{ik,jl}=X_{ij,kl}$ is realignment, $r_k(X)=\operatorname{Tr}[(R(X)R(X)^*)^k]$, and all traces are ordinary unnormalized matrix traces. We write $t=\operatorname{Tr}X$, $X_A=\operatorname{Tr}_B X$, $X_B=\operatorname{Tr}_A X$, $\widetilde X=tX-X_A\otimes X_B$, $\widetilde r_k=r_k(\widetilde X)$, and $G=(t^2-\operatorname{Tr}X_A^2)(t^2-\operatorname{Tr}X_B^2)$. The notation $q_k$ means $\operatorname{Tr}[(X^{\Gamma_B})^k]$, where $\Gamma_B$ transposes the B factor.
-- source:
--   Optimal entanglement criteria from trace invariants, arXiv:2609.29471v1, PDF p. 36, Proposition 5.12

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P19

/-- Proposition 5.12; arXiv:2609.29471v1, PDF pp.36. -/
theorem discrete_separability_bounds (m : ℕ) (hm : 1 ≤ m) (a b : ℕ) (ha : 0<a) (hb : 0<b)
    (X : Bip a b) (hX : QAlgorithms.Entanglement.IsSeparablePositive X) (ht : 0 < mass X) :
    alpha (fun k : Fin m => rMoment (((mass X)⁻¹ : ℂ) • X) (k.val+1)) ≤
      ENNReal.ofReal (QAlgorithms.traceNorm (realignmentSquare X)/mass X) ∧
    QAlgorithms.traceNorm (realignmentSquare X)/mass X ≤ 1 ∧
    (0<G X →
      alpha (fun k : Fin m => rMoment (((Real.sqrt (G X))⁻¹ : ℂ) • centered X) (k.val+1)) ≤
        ENNReal.ofReal (QAlgorithms.traceNorm (realignmentSquare (centered X))/Real.sqrt (G X)) ∧
      QAlgorithms.traceNorm (realignmentSquare (centered X))/Real.sqrt (G X) ≤ 1) := by sorry

end QAlgorithms.Papers.Independent.Information100.P19

end
