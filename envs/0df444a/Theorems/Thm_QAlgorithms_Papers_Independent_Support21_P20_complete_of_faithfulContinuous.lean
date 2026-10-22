-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P20_complete_of_faithfulContinuous
-- name    : QAlgorithms.Papers.Independent.Support21.P20.complete_of_faithfulContinuous
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T05:01:55.406073+00:00
-- url     : https://prove2.me/theorems/12186d13-89b0-4dd2-b18a-dcee4ef58fb9
-- title:
--   A faithful finite continuous valuation forces completeness
-- statement:
--   Let $A$ be a Boolean algebra admitting suprema of countable subsets, and let $\nu:A\to[0,\infty)$ be a faithful finite positive continuous valuation. Faithfulness means $\nu(a)=0$ implies $a=0$, and continuity concerns every existing supremum of a nonempty directed subset. Then
--
--   $$\text{every subset of }A\text{ has a supremum}.$$
--
--   In addition, if $B$ is any complete Boolean algebra and $f:A\to B$ is a unital Boolean homomorphism preserving countable suprema, then
--
--   $$f(\sup S)=\sup f(S)\qquad\text{for every }S\subseteq A.$$
--
--   Both the empty subset and the one-element Boolean algebra are included. No injectivity or measure preservation of $f$ is required. This supplies both conclusions of the lemma without assuming completeness of $A$ in advance.
-- source:
--   Gelfand-type duality for commutative von Neumann algebras, arXiv:2005.05284v3, PDF p. 36, Lemma 4.55

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P20

namespace QAlgorithms.Papers.Independent.Support21.P20

open Set Filter

open scoped NNReal

universe u v

/-- Lemma 4.55, PDF pp.36–37: completeness and preservation of arbitrary suprema. -/
theorem complete_of_faithfulContinuous (A : Type u) [BooleanAlgebra A]
    (nu : A → ℝ≥0) (hnu : IsPositiveContinuousValuation nu)
    (hfaithful : ∀ a, nu a = 0 → a = ⊥)
    (hcountable : ∀ s : Set A, s.Countable → ∃ a : A, IsLUB s a) :
    (∀ s : Set A, ∃ a : A, IsLUB s a) ∧
    ∀ (B : Type v) [CompleteBooleanAlgebra B] (f : BoundedLatticeHom A B),
      (∀ (s : Set A) (a : A), s.Countable → IsLUB s a → IsLUB (f '' s) (f a)) →
      ∀ (s : Set A) (a : A), IsLUB s a → IsLUB (f '' s) (f a) := by sorry

end QAlgorithms.Papers.Independent.Support21.P20
