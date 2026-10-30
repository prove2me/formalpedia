-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P06_chosenLifts_give_bicategoryEquivalence
-- name    : QAlgorithms.Papers.Independent.Bridge50.P06.chosenLifts_give_bicategoryEquivalence
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:13:44.833428+00:00
-- url     : https://prove2.me/theorems/e420338a-998f-4c53-b32e-d5b388b879c3
-- title:
--   Chosen lifts reconstruct an inverse pseudofunctor
-- statement:
--   Let $\mathcal C$ and $\mathcal D$ be arbitrary bicategories and let $F:\mathcal C\to\mathcal D$ be a pseudofunctor. Assume that for every pair of parallel 1-morphisms $f,g$ of $\mathcal C$, the function induced by $F$ on 2-morphisms from $f$ to $g$ is bijective.
--
--   Suppose the following data have been chosen:
--
--   1. For every object $Y$ of $\mathcal D$, an object $L_Y$ of $\mathcal C$ and an adjoint equivalence $\xi_Y:Y\to F(L_Y)$ with chosen inverse $\bar\xi_Y$.
--   2. For every $X_1,X_2\in\mathcal C$ and every 1-morphism $g:F(X_1)\to F(X_2)$, a 1-morphism $L_g:X_1\to X_2$ and a 2-isomorphism $\eta_g:g\Rightarrow F(L_g)$.
--
--   There exist a pseudofunctor $G:\mathcal D\to\mathcal C$ and pseudonatural equivalences
--
--   $$
--   a:\operatorname{id}_{\mathcal D}\Rightarrow F\circ G,
--   \qquad b:G\circ F\Rightarrow\operatorname{id}_{\mathcal C}.
--   $$
--
--   They can be chosen with precisely the prescribed object and 1-morphism assignments
--
--   $$
--   G(Y)=L_Y,\qquad
--   G(g)=L_{\widetilde g},\qquad
--   \widetilde g=(\xi_{Y_2}\circ g)\circ\bar\xi_{Y_1}
--   \quad(g:Y_1\to Y_2),
--   $$
--
--   and with object components $a_Y=\xi_Y$ and $b_X=L_{\bar\xi_{F(X)}}$. Thus $F$ is an equivalence of bicategories.
--
--   This criterion reconstructs an inverse from independently chosen lifts while retaining arbitrary, possibly noninvertible, 2-morphisms in the bicategories.
--
--   **Formalization Note** The equivalences $a,b$ are adjoint equivalences in Mathlib's bicategory of pseudofunctors, strong transformations and modifications. Their inverse transformations and invertible modifications are included. Heterogeneous equality transports the prescribed arrows along equality of the object functions; it does not weaken the arrow formulas.
-- source:
--   Four Equivalent Versions of Non-Abelian Gerbes, arXiv:1103.4815v3, PDF p. 60, Lemma B.1

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P06

namespace QAlgorithms.Papers.Independent.Bridge50.P06

open CategoryTheory

open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans

universe uC uD vC vD wC wD

variable {C : Type uC} [Bicategory.{wC, vC} C]

variable {D : Type uD} [Bicategory.{wD, vD} D]

/-- Lemma B.1, arXiv:1103.4815v3, PDF pp. 59--61.
A locally fully faithful pseudofunctor with the specified chosen object and
1-morphism lifts admits an inverse pseudofunctor and pseudonatural equivalences.
The inverse has precisely the chosen object function and the arrow formula
G(g) = G_tilde(g). The equivalences live in the bicategory of pseudofunctors,
so their inverses and invertible modifications, with zigzag identities, are
included. The object components of a and b are the paper's prescribed ones.
`HEq` only transports arrows along equality of the object functions. -/
theorem chosenLifts_give_bicategoryEquivalence
    (F : Pseudofunctor C D) (hF : LocallyFullyFaithful F) (L : ChosenLifts F) :
    ∃ G : Pseudofunctor D C,
      G.obj = L.objectLift ∧
      (∀ (Y1 Y2 : D) (g : Y1 ⟶ Y2), HEq (G.map g) (inverseArrow L g)) ∧
      ∃ (a : Bicategory.Equivalence (Pseudofunctor.id D) (G.comp F))
        (b : Bicategory.Equivalence (F.comp G) (Pseudofunctor.id C)),
        (∀ Y : D, HEq (a.hom.app Y) (L.objectComparison Y).hom) ∧
        (∀ X : C, HEq (b.hom.app X) (inverseCounitComponent L X)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P06
