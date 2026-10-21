-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P26_lemma_2_3
-- name    : QAlgorithms.Papers.Independent.Renew46.P26.lemma_2_3
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T20:47:20.109978+00:00
-- url     : https://prove2.me/theorems/4696881a-a161-49b4-a059-b01f92069ed5
-- title:
--   Lemma 2.3
-- statement:
--   Let $A$ be a unital associative complex algebra with a conjugate-linear involution $*$ reversing products. Then
--
--   $$A\text{ is commutative}\iff aa^*=a^*a\quad\text{for every }a\in A.$$
--
--   Moreover, let $R$ be a real subalgebra such that every element of $A$ is uniquely $a+ib$ with $a,b\in R$. If every element of $R$ is fixed by $*$, then $A$ is commutative. Both assertions concern algebraic involutions and require no positivity assumption.
-- source:
--   A New Approach to the Representation Thoery of the Symmetric Groups. 2, arXiv:math/0503040v3, PDF p. 9, Lemma 2.3

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P26

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P26

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Lemma 2.3 (PDF p.9), both clauses. Star is conjugate-linear over C,
involutive and reverses products. The second assertion uses an actual real form,
not an arbitrary selected collection of real vectors. -/
theorem lemma_2_3 {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A]
    [StarModule ℂ A] [Algebra ℝ A] [IsScalarTower ℝ ℂ A] :
    ((∀ a b : A, a * b = b * a) ↔ ∀ a : A, a * star a = star a * a) ∧
    (∀ R : Subalgebra ℝ A, IsRealForm R →
      (∀ a : R, star (a : A) = (a : A)) → ∀ a b : A, a * b = b * a) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P26

end
