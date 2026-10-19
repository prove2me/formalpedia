-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P19_homogeneous_moment_hierarchy
-- name    : QAlgorithms.Papers.Independent.Information100.P19.homogeneous_moment_hierarchy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:00:52.199338+00:00
-- url     : https://prove2.me/theorems/21710d02-4401-412d-a6eb-a0c1252dc4e7
-- title:
--   §5.3 unnumbered: all polynomial separability inequalities (26)–(30)
-- statement:
--   Every unnormalized separable $X$, with $t=\operatorname{Tr}X$, satisfies the interpolation, pair-sum and first two minorant inequalities
--   $$r_1^3\le r_2t^2,\quad r_1^2+2t^2r_1\le2r_2+t^4,\quad r_1\le t^2,\quad \tfrac32r_1t^2-\tfrac12r_2\le t^4.$$
--   For any $p(x)=\sum_{k=1}^m p_kx^k\le\sqrt x$ on $[0,1]$,
--   $$\sum_{k=1}^m p_kr_k(X)t^{2(m-k)}\le t^{2m},\qquad
--   \sum_{k=1}^m p_kr_k(\widetilde X)G^{m-k}\le G^m.$$
--   The first two displayed nonlinear inequalities also hold after replacing $X$ by $\widetilde X$ and $t^2$ by $G$. The second binomial defect belongs to the separable cone and has no PSD-valid one-matrix diagonal-embedding representative. All expressions remain polynomial at $t=0$ or $G=0$.
--
--   Here $R(X)_{ik,jl}=X_{ij,kl}$ is realignment, $r_k(X)=\operatorname{Tr}[(R(X)R(X)^*)^k]$, and all traces are ordinary unnormalized matrix traces. We write $t=\operatorname{Tr}X$, $X_A=\operatorname{Tr}_B X$, $X_B=\operatorname{Tr}_A X$, $\widetilde X=tX-X_A\otimes X_B$, $\widetilde r_k=r_k(\widetilde X)$, and $G=(t^2-\operatorname{Tr}X_A^2)(t^2-\operatorname{Tr}X_B^2)$. The notation $q_k$ means $\operatorname{Tr}[(X^{\Gamma_B})^k]$, where $\Gamma_B$ transposes the B factor.
-- source:
--   Optimal entanglement criteria from trace invariants, arXiv:2609.29471v1, PDF p. 36, §5.3 unnumbered: all polynomial separability inequalities (26)–(30)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P19

/-- §5.3 unnumbered: all polynomial separability inequalities (26)–(30); arXiv:2609.29471v1, PDF pp.36, 37. -/
theorem homogeneous_moment_hierarchy  :
    (∀ a b, 0<a → 0<b → ∀ X : Bip a b,
      QAlgorithms.Entanglement.IsSeparablePositive X →
      rMoment X 1^3 ≤ rMoment X 2*mass X^2 ∧
      rMoment X 1^2+2*mass X^2*rMoment X 1 ≤ 2*rMoment X 2+mass X^4 ∧
      rMoment X 1 ≤ mass X^2 ∧
      (3/2 : ℝ)*rMoment X 1*mass X^2-(1/2 : ℝ)*rMoment X 2 ≤ mass X^4 ∧
      rMoment (centered X) 1^3 ≤ rMoment (centered X) 2*G X ∧
      rMoment (centered X) 1^2+2*G X*rMoment (centered X) 1 ≤
        2*rMoment (centered X) 2+G X^2 ∧
      ∀ m : ℕ, 1 ≤ m → ∀ p : Fin m → ℝ,
        (∀ x ∈ Set.Icc (0:ℝ) 1, polynomialEval p x ≤ Real.sqrt x) →
        (∑ k, p k*rMoment X (k.val+1)*mass X^(2*(m-(k.val+1)))) ≤ mass X^(2*m) ∧
        (∑ k, p k*rMoment (centered X) (k.val+1)*G X^(m-(k.val+1))) ≤ G X^m) ∧
    b11-b2 ∈ psdCone 2 ∧ wM ∈ sepCone 4 ∧
    ¬ (∃ f ∈ psdCone 4, ∀ a b, 0<a → 0<b → ∀ X : Bip a b, X.IsHermitian →
      tensorEval (embed false f) X = tensorEval wM X) := by sorry

end QAlgorithms.Papers.Independent.Information100.P19

end
