-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P20_weakAE_implies_strictAE_of_separated
-- name    : QAlgorithms.Papers.Independent.Support21.P20.weakAE_implies_strictAE_of_separated
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T05:01:13.03497+00:00
-- url     : https://prove2.me/theorems/4a6afa7e-e726-4292-a4ed-1f5fd76ab950
-- title:
--   Weak and strict equality agree into a countably separated target
-- statement:
--   An enhanced space $Y$ is countably separated if a countable family of measurable subsets covers $Y$ and, for every ordered pair of distinct points $y,y'$, contains a set containing $y$ but not $y'$. Let $X$ be any enhanced space and assume $Y$ is countably separated. Then, for premaps $f,g:X\rightharpoonup Y$,
--
--   $$f\approx g\quad\Longrightarrow\quad f\sim g.$$
--
--   The identity-on-representatives map $[f]_{\sim}\mapsto[f]_{\approx}$ is therefore bijective on these hom quotients. Restricted to countably separated objects on both sides, the quotient functor is an equivalence. The source need not be countably separated for the hom-set assertion. The covering condition handles disagreements involving undefined values, including singleton targets.
-- source:
--   Gelfand-type duality for commutative von Neumann algebras, arXiv:2005.05284v3, PDF p. 32, Lemma 4.22

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P20

namespace QAlgorithms.Papers.Independent.Support21.P20

open Set Filter

open scoped NNReal

universe u v

/-- Lemma 4.22, PDF p.32: separation is imposed only on the target.
The specified bijections of hom quotients express the equivalence on separated spaces. -/
theorem weakAE_implies_strictAE_of_separated (X Y : Type u)
    (E : Enhanced X) (F : Enhanced Y) (hF : IsCountablySeparated F) :
    (∀ f g : Premap E F, WeakAE E F f.val g.val → StrictAE E f.val g.val) ∧
    ∃ q : Quot (strictHomRelation E F) → Quot (weakHomRelation E F),
      Function.Bijective q ∧ ∀ f : Premap E F,
        q (Quot.mk (strictHomRelation E F) f) = Quot.mk (weakHomRelation E F) f := by sorry

end QAlgorithms.Papers.Independent.Support21.P20
