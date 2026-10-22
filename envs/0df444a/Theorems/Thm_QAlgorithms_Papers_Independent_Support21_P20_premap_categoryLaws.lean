-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P20_premap_categoryLaws
-- name    : QAlgorithms.Papers.Independent.Support21.P20.premap_categoryLaws
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:58:32.028368+00:00
-- url     : https://prove2.me/theorems/3d8541fc-6f52-4a23-ab37-956905f65329
-- title:
--   The category laws for partial enhanced premaps
-- statement:
--   An enhanced measurable space is a triple $(X,\mathcal M_X,\mathcal N_X)$ with a sigma-algebra $\mathcal M_X$ and a sigma-ideal $\mathcal N_X$ of all subsets of $X$, contained in $\mathcal M_X$. A premap $f:X\rightharpoonup Y$ has conegligible domain and pulls measurable sets back to measurable sets and negligible sets back to negligible sets. Identity maps are premaps, and compositions are premaps with
--
--   $$\operatorname{pdom}(g\circ f)=\operatorname{pdom}f\cap f^{-1}(\operatorname{pdom}g).$$
--
--   Partial composition is associative and satisfies both identity laws. Thus these objects and actual partial maps form the category $\mathbf{PreEMS}$. Undefined values are represented by a separate optional value, so even an empty target is permitted when the source is entirely negligible.
-- source:
--   Gelfand-type duality for commutative von Neumann algebras, arXiv:2005.05284v3, PDF p. 29, Proposition 4.7

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P20

namespace QAlgorithms.Papers.Independent.Support21.P20

open Set Filter

open scoped NNReal

universe u v

/-- Proposition 4.7, PDF p.29: closure, actual domain formula, and all category laws. -/
theorem premap_categoryLaws :
    (∀ (X : Type u) (E : Enhanced X), IsPremap E E (fun x => some x)) ∧
    (∀ (X Y Z : Type u) (E : Enhanced X) (F : Enhanced Y) (G : Enhanced Z)
      (f : Premap E F) (g : Premap F G),
      IsPremap E G (partialCompose g.val f.val) ∧
      partialDomain (partialCompose g.val f.val) =
        partialDomain f.val ∩ partialPreimage f.val (partialDomain g.val)) ∧
    (∀ (X Y Z W : Type u) (E : Enhanced X) (F : Enhanced Y)
      (G : Enhanced Z) (H : Enhanced W)
      (f : Premap E F) (g : Premap F G) (h : Premap G H),
      partialCompose h.val (partialCompose g.val f.val) =
        partialCompose (partialCompose h.val g.val) f.val) ∧
    (∀ (X Y : Type u) (E : Enhanced X) (F : Enhanced Y) (f : Premap E F),
      partialCompose (fun y => some y) f.val = f.val ∧
      partialCompose f.val (fun x => some x) = f.val) := by sorry

end QAlgorithms.Papers.Independent.Support21.P20
