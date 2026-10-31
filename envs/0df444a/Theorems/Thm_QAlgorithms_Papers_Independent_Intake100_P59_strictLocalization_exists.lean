-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P59_strictLocalization_exists
-- name    : QAlgorithms.Papers.Independent.Intake100.P59.strictLocalization_exists
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:04:30.799557+00:00
-- url     : https://prove2.me/theorems/898bfc2c-4417-498b-b9a3-3261d6f653f5
-- title:
--   Existence of localization with strict unique factorization
-- statement:
--   Let $C$ be a category and $W$ any class of arrows. The canonical path construction adjoining formal inverses and quotienting by the category and inverse relations gives $Q:C\to C[W^{-1}]$, inverting $W$. For every target category $E$ and every functor $\Phi:C\to E$ inverting $W$, there exists exactly one functor $\Psi:C[W^{-1}]\to E$ such that
--
--   $$
--   \Psi\circ Q=\Phi.
--   $$
--
--   This supplies the strict localization of Section 3.1 without calculus-of-fractions hypotheses. The hom universe is enlarged when necessary; $W$ need not be nonempty or closed under composition.
-- source:
--   Orbifolds as stacks?, arXiv:0806.4160v2, PDF p. 9, Lemma 3.14

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P59

namespace QAlgorithms.Papers.Independent.Intake100.P59

open CategoryTheory

universe u v uC vC uD vD uE vE

/-- Lemma 3.14, PDF pp.9–10: the canonical path-and-congruence-quotient
localization exists and has the strict unique-factorization property for every
target category. Mathlib's `W.Localization` and `W.Q` are the actual construction,
with hom universes enlarged to contain paths through arbitrary objects of C.
No calculus-of-fractions assumption is imposed on W. -/
theorem strictLocalization_exists
    {C : Type uC} [Category.{vC} C] (W : MorphismProperty C) :
    ∀ (E : Type uE) [Category.{vE} E],
      Nonempty (Localization.StrictUniversalPropertyFixedTarget W.Q W E) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P59
