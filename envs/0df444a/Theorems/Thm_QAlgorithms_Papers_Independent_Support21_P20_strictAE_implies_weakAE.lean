-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P20_strictAE_implies_weakAE
-- name    : QAlgorithms.Papers.Independent.Support21.P20.strictAE_implies_weakAE
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T05:00:43.16948+00:00
-- url     : https://prove2.me/theorems/44d37625-e3be-449d-b274-b9134ddd4d80
-- title:
--   EMS is a quotient of StrictEMS
-- statement:
--   Let $X,Y$ be arbitrary enhanced measurable spaces. For all premaps $f,g:X\rightharpoonup Y$,
--
--   $$f\sim g\quad\Longrightarrow\quad f\approx g.$$
--
--   Consequently the identity on premap representatives induces a surjection from the strict hom quotient to the weak hom quotient, sending $[f]_{\sim}$ to $[f]_{\approx}$. The congruence laws show that these prescribed maps form the identity-on-objects quotient functor $\mathbf{StrictEMS}\to\mathbf{EMS}$. No separation assumption is required.
-- source:
--   Gelfand-type duality for commutative von Neumann algebras, arXiv:2005.05284v3, PDF p. 31, Lemma 4.20

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P20

namespace QAlgorithms.Papers.Independent.Support21.P20

open Set Filter

open scoped NNReal

universe u v

/-- Lemma 4.20, PDF p.31: the identity-on-representatives quotient is surjective.
Together with the congruence laws this expresses the quotient functor StrictEMS → EMS. -/
theorem strictAE_implies_weakAE (X Y : Type u) (E : Enhanced X) (F : Enhanced Y) :
    (∀ f g : Premap E F, StrictAE E f.val g.val → WeakAE E F f.val g.val) ∧
    ∃ q : Quot (strictHomRelation E F) → Quot (weakHomRelation E F),
      Function.Surjective q ∧ ∀ f : Premap E F,
        q (Quot.mk (strictHomRelation E F) f) = Quot.mk (weakHomRelation E F) f := by sorry

end QAlgorithms.Papers.Independent.Support21.P20
