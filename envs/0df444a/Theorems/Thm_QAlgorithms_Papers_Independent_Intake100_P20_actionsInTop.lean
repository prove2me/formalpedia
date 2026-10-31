-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P20_actionsInTop
-- name    : QAlgorithms.Papers.Independent.Intake100.P20.actionsInTop
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:29:34.534998+00:00
-- url     : https://prove2.me/theorems/d0ad75b7-607f-45c8-a11e-776d5ed5cb9b
-- title:
--   Actions in Top are jointly continuous actions
-- statement:
--   Let $G$ be a topological group, let $X$ be any topological space, and let $n:G\times X\to X$. The map defines an action in Top if and only if it is the scalar multiplication of an ordinary left action and is jointly continuous. Its requirements are
--
--   $$n(1,x)=x,\qquad n(gh,x)=n(g,n(h,x)),\qquad n:G\times X\to X\text{ continuous}.$$
--
--   The recovered action has exactly the given map, and neither space is assumed compact or separated. This transports the Set action correspondence to Top.
-- source:
--   Group Objects and Internal Categories, arXiv:math/0212065v1, PDF p. 5, §1, Group Actions

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P20

namespace QAlgorithms.Papers.Independent.Intake100.P20

open CategoryTheory

open scoped TensorProduct Manifold ContDiff

universe u v w z

/-- PDF p. 5: actions in Top are jointly continuous ordinary actions.
There is no separation, compactness, or nonemptiness hypothesis on X. -/
theorem actionsInTop {G : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {X : Type v} [TopologicalSpace X] (n : G × X → X) :
    (ActionDiagrams n ∧ Continuous n) ↔
      ∃ a : MulAction G X,
        (∀ g x, @SMul.smul G X a.toSMul g x = n (g, x)) ∧
        (letI : MulAction G X := a; ContinuousSMul G X) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P20
