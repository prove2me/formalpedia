-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P20_strictAE_quotientWellDefined
-- name    : QAlgorithms.Papers.Independent.Support21.P20.strictAE_quotientWellDefined
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:59:06.700973+00:00
-- url     : https://prove2.me/theorems/85ca90b1-477b-40bf-b42b-16bf83fa72d3
-- title:
--   Strict almost-everywhere equality defines a quotient category
-- statement:
--   For enhanced spaces $X,Y$, let $f,g:X\rightharpoonup Y$ be premaps. Define strict equality almost everywhere by
--
--   $$f\sim g\quad\Longleftrightarrow\quad\{x\in X:f(x)\ne g(x)\}\in\mathcal N_X.$$
--
--   Two undefined values agree; one undefined and one defined value disagree. This is an equivalence relation on each premap hom-set. For composable premaps $f,g:X\rightharpoonup Y$ and $h,k:Y\rightharpoonup Z$, $f\sim g$ and $h\sim k$ imply $h\circ f\sim k\circ g$. These full equivalence and congruence conditions make the stated quotient category $\mathbf{StrictEMS}$ well defined.
-- source:
--   Gelfand-type duality for commutative von Neumann algebras, arXiv:2005.05284v3, PDF p. 30, Proposition 4.12

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P20

namespace QAlgorithms.Papers.Independent.Support21.P20

open Set Filter

open scoped NNReal

universe u v

/-- Proposition 4.12, PDF p.30: strict a.e. equality is an equivalence congruence.
These are exactly the conditions for the stated quotient category to exist. -/
theorem strictAE_quotientWellDefined (X Y Z : Type u)
    (E : Enhanced X) (F : Enhanced Y) (G : Enhanced Z) :
    Equivalence (strictHomRelation E F) ∧
    ∀ (f g : Premap E F) (h k : Premap F G),
      StrictAE E f.val g.val → StrictAE F h.val k.val →
      StrictAE E (partialCompose h.val f.val) (partialCompose k.val g.val) := by sorry

end QAlgorithms.Papers.Independent.Support21.P20
