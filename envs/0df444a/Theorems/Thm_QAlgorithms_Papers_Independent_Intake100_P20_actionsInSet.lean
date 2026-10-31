-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P20_actionsInSet
-- name    : QAlgorithms.Papers.Independent.Intake100.P20.actionsInSet
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:28:54.68374+00:00
-- url     : https://prove2.me/theorems/7aa95a7e-e2b9-49b8-a304-2362fdbb0bb1
-- title:
--   Diagrammatic actions are ordinary left actions
-- statement:
--   Let $M$ be a monoid (in particular a group), let $X$ be any set, and fix $n:M\times X\to X$. The diagrammatic action axioms are exactly
--
--   $$n(1,x)=x,\qquad n(ab,x)=n(a,n(b,x)).$$
--
--   They hold if and only if there is an ordinary left $M$-action whose scalar multiplication is $a\cdot x=n(a,x)$. The correspondence preserves the actual action map. This includes the source's monoid extension on page 5 and permits the empty set $X$.
-- source:
--   Group Objects and Internal Categories, arXiv:math/0212065v1, PDF p. 4, §1, Group Actions, pp. 4–5

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P20

namespace QAlgorithms.Papers.Independent.Intake100.P20

open CategoryTheory

open scoped TensorProduct Manifold ContDiff

universe u v w z

/-- PDF pp. 4–5: diagrammatic actions in Set are ordinary left actions,
preserving the given map. As the source observes, this includes monoids.
The type X is allowed to be empty. -/
theorem actionsInSet {M : Type u} [Monoid M] {X : Type v} (n : M × X → X) :
    ActionDiagrams n ↔
      ∃ a : MulAction M X, ∀ g x, @SMul.smul M X a.toSMul g x = n (g, x) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P20
