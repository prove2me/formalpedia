-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P20_weakAE_quotientWellDefined
-- name    : QAlgorithms.Papers.Independent.Support21.P20.weakAE_quotientWellDefined
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:59:49.197001+00:00
-- url     : https://prove2.me/theorems/89ad42ce-461f-4461-a7c9-f3792eae1f19
-- title:
--   Weak almost-everywhere equality defines EMS
-- statement:
--   For enhanced spaces $X,Y$, weak equality almost everywhere of premaps $f,g:X\rightharpoonup Y$ means
--
--   $$f\approx g\quad\Longleftrightarrow\quad\forall m\in\mathcal M_Y,\ f^{-1}(m)\mathbin{\triangle}g^{-1}(m)\in\mathcal N_X.$$
--
--   This is an equivalence relation on every premap hom-set and a congruence for composition: $f\approx g$ and $h\approx k$ imply $h\circ f\approx k\circ g$ for composable premaps. Together with the partial-map category laws, this proves that the quotient category $\mathbf{EMS}$ is well defined. The assertion concerns weak equality throughout; its definition does not identify maps merely on the intersection of their domains.
-- source:
--   Gelfand-type duality for commutative von Neumann algebras, arXiv:2005.05284v3, PDF p. 30, Proposition 4.14

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P20

namespace QAlgorithms.Papers.Independent.Support21.P20

open Set Filter

open scoped NNReal

universe u v

/-- Proposition 4.14, PDF pp.30–31: the weak relation is an equivalence congruence.
The proof's stray strict-equality symbol is read using its displayed preimage argument. -/
theorem weakAE_quotientWellDefined (X Y Z : Type u)
    (E : Enhanced X) (F : Enhanced Y) (G : Enhanced Z) :
    Equivalence (weakHomRelation E F) ∧
    ∀ (f g : Premap E F) (h k : Premap F G),
      WeakAE E F f.val g.val → WeakAE F G h.val k.val →
      WeakAE E G (partialCompose h.val f.val) (partialCompose k.val g.val) := by sorry

end QAlgorithms.Papers.Independent.Support21.P20
