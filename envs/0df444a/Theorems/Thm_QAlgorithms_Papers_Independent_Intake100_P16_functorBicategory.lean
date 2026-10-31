-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P16_functorBicategory
-- name    : QAlgorithms.Papers.Independent.Intake100.P16.functorBicategory
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:21:25.241056+00:00
-- url     : https://prove2.me/theorems/9e011eac-9f69-4f04-9c02-64571459ad1e
-- title:
--   The bicategory of pseudofunctors, transformations and modifications
-- statement:
--   Let $S,T$ be arbitrary bicategories in compatible universes. Pseudofunctors $S\to T$, pseudonatural transformations between them, and modifications form a bicategory $\mathrm{Funct}(S,T)$. The identities and composition of transformations are given pointwise by the corresponding operations in $T$; identities and vertical composition of modifications, both whiskerings, and the associators and unitors are also the corresponding pointwise operations in $T$.
--
--   Writing $\eta:F\Rightarrow G$, $\theta:G\Rightarrow H$ and $X\in S$, the defining object components include
--   $$
--   (\theta\circ\eta)_X=\theta_X\circ\eta_X,\qquad
--   (\mathrm{id}_F)_X=\mathrm{id}_{F(X)}.
--   $$
--   All bicategory coherence laws hold. If $T$ is strict, this bicategory is strict.
--
--   This provides the ambient bicategory in which pseudonatural equivalences and modifications of pseudofunctors are interpreted. The universal converse about strictness is a separate deferred source-ambiguity node, since $S$ may be empty.
--
--   **Formalization Note** The statement uses Mathlib's canonical bicategory, pins its 1-cell type and pointwise operations, and retains only the valid sufficient direction of the following source sentence. The extra unit field of Mathlib's strong transformations is redundant by Lemma A.7.
-- source:
--   Local Theory for 2-Functors on Path 2-Groupoids, arXiv:1303.4663v1, PDF p. 47, functor-bicategory

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P16

namespace QAlgorithms.Papers.Independent.Intake100.P16

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.MonoidalCategory

open scoped CategoryTheory.Pseudofunctor.StrongTrans

universe uS vS wS uT vT wT uC vC

/-- Appendix A, PDF p.47: the canonical bicategory of pseudofunctors,
pseudonatural transformations and modifications, including its pointwise
compositions and coherence maps. Strictness of T is sufficient. The false
universal converse is a separate deferred node. Mathlib's extra unit axiom
for strong transformations is redundant by Lemma A.7. -/
theorem functorBicategory
    (S : Type uS) [Bicategory.{wS, vS} S]
    (T : Type uT) [Bicategory.{wT, vT} T] :
    Nonempty (Bicategory (Pseudofunctor S T)) ∧
    (∀ F G : Pseudofunctor S T, (F ⟶ G) = Pseudofunctor.StrongTrans F G) ∧
    (∀ (F : Pseudofunctor S T) (X : S), Pseudofunctor.StrongTrans.app (𝟙 F) X = 𝟙 (F.obj X)) ∧
    (∀ {F G H : Pseudofunctor S T} (r : F ⟶ G) (s : G ⟶ H) (X : S),
      (r ≫ s).app X = r.app X ≫ s.app X) ∧
    (∀ {F G : Pseudofunctor S T} (r : F ⟶ G) (X : S),
      (Pseudofunctor.StrongTrans.Hom.as (𝟙 r)).app X = 𝟙 (r.app X)) ∧
    (∀ {F G : Pseudofunctor S T} {r s t : F ⟶ G}
      (a : r ⟶ s) (b : s ⟶ t) (X : S),
      (a ≫ b).as.app X = a.as.app X ≫ b.as.app X) ∧
    (∀ {F G H : Pseudofunctor S T} (r : F ⟶ G) {s t : G ⟶ H}
      (a : s ⟶ t) (X : S),
      (r ◁ a).as.app X = r.app X ◁ a.as.app X) ∧
    (∀ {F G H : Pseudofunctor S T} {r s : F ⟶ G} (a : r ⟶ s)
      (t : G ⟶ H) (X : S),
      (a ▷ t).as.app X = a.as.app X ▷ t.app X) ∧
    (∀ {F G H I : Pseudofunctor S T} (r : F ⟶ G) (s : G ⟶ H)
      (t : H ⟶ I) (X : S),
      (Bicategory.associator r s t).hom.as.app X = (Bicategory.associator (r.app X) (s.app X) (t.app X)).hom) ∧
    (∀ {F G : Pseudofunctor S T} (r : F ⟶ G) (X : S),
      (Bicategory.leftUnitor r).hom.as.app X = (Bicategory.leftUnitor (r.app X)).hom ∧
      (Bicategory.rightUnitor r).hom.as.app X = (Bicategory.rightUnitor (r.app X)).hom) ∧
    (Bicategory.Strict T → Bicategory.Strict (Pseudofunctor S T)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P16
