-- Prove2me | Theorems.Thm_TwoCategory_smallBasedCategory_exists_isWeakTwoPullback_fibered
-- name    : TwoCategory.smallBasedCategory_exists_isWeakTwoPullback_fibered
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T16:29:28.259978+00:00
-- url     : https://prove2.me/theorems/e1be9d6a-d43d-43d1-a5f9-ae32d511b0e4
-- title:
--   2-fibre products of small fibered categories over $\mathcal D$ exist and are computed in $\mathbf{Cat}/\mathcal D$
-- statement:
--   Existence of 2-fibre products in the 2-category of fibered categories over a base category, computed as 2-fibre products of categories over the base.
--
--   **2-fibre products.** Let $\mathcal C$ be a 2-category (or a bicategory) and let $f:B\to A$, $g:C\to A$ be 1-morphisms. A *2-commutative square over $(f,g)$* is a quadruple $(D,a,b,\phi)$ consisting of an object $D$, 1-morphisms $a:D\to B$, $b:D\to C$ and a 2-isomorphism $\phi:f\circ a\Rightarrow g\circ b$. A *morphism of squares* $(D',c,d,\psi)\to(D,a,b,\phi)$ is a triple $(k,\alpha,\beta)$ with $k:D'\to D$ a 1-morphism and $\alpha:c\Rightarrow a\circ k$, $\beta:d\Rightarrow b\circ k$ 2-isomorphisms such that
--
--   $$(1_g\star\beta)\odot\psi=(\phi\star 1_k)\odot(1_f\star\alpha)$$
--
--   as 2-morphisms $f\circ c\Rightarrow g\circ b\circ k$ ($\odot$ is vertical and $\star$ horizontal composition). The square $(P,a,b,\phi)$ is a *2-fibre product* of $(f,g)$ (Definitions E.5.6.1 and E.5.6.2 of the source: a final object of the 2-category $\mathbf{Diagrams}(f,g)$) if
--
--   1. every 2-commutative square over $(f,g)$ admits a morphism of squares to $(P,a,b,\phi)$, and
--   2. for any two morphisms of squares $(k,\alpha,\beta)$, $(k',\alpha',\beta')$ from the same square to $(P,a,b,\phi)$ there is a unique 2-isomorphism $\gamma:k\Rightarrow k'$ with $(1_a\star\gamma)\odot\alpha=\alpha'$ and $(1_b\star\gamma)\odot\beta=\beta'$.
--
--   Only invertible 2-morphisms occur in this definition, so a 2-fibre product in $\mathcal C$ is the same thing as a 2-fibre product in the strict $(2,1)$-category $\mathcal C^{\mathrm{strict}}$ obtained from $\mathcal C$ by discarding the non-invertible 2-morphisms.
--
--   **Categories over $\mathcal D$.** Let $\mathcal D$ be a category. A *category over $\mathcal D$* is a pair $(\mathcal S,p)$ of a category $\mathcal S$ and a functor $p:\mathcal S\to\mathcal D$. The 2-category $\mathbf{Cat}/\mathcal D$ (Example E.5.7.2 of the source) has the categories over $\mathcal D$ as objects; its 1-morphisms $(\mathcal S,p)\to(\mathcal S',p')$ are the functors $F:\mathcal S\to\mathcal S'$ with $p'\circ F=p$ (equality of functors), and its 2-morphisms $t:F\Rightarrow F'$ are the natural transformations with $p'(t_A)=1_{p(A)}$ for every object $A$ of $\mathcal S$.
--
--   **Fibered categories.** Let $p:\mathcal S\to\mathcal D$ be a category over $\mathcal D$. A morphism $\varphi:a\to b$ of $\mathcal S$ is *strongly cartesian* (Definition E.5.7.5) if for every object $c$ of $\mathcal S$ the map
--
--   $$\mathrm{Hom}_{\mathcal S}(c,a)\to\mathrm{Hom}_{\mathcal S}(c,b)\times_{\mathrm{Hom}_{\mathcal D}(p(c),p(b))}\mathrm{Hom}_{\mathcal D}(p(c),p(a)),\qquad g\mapsto(\varphi\circ g,\ p(g)),$$
--
--   is a bijection. The category $(\mathcal S,p)$ is *fibered over $\mathcal D$* (Definition E.5.7.7) if for every object $a$ of $\mathcal S$ and every morphism $f:U\to p(a)$ of $\mathcal D$ there is a strongly cartesian morphism $\varphi:f^*a\to a$ with $p(\varphi)=f$. A 1-morphism of $\mathbf{Cat}/\mathcal D$ *preserves strongly cartesian morphisms* if it maps strongly cartesian morphisms of its source to strongly cartesian morphisms of its target. The 2-category $\mathbf{Fib}/\mathcal D$ (Example E.5.7.8) is the sub-2-category of $\mathbf{Cat}/\mathcal D$ whose objects are the fibered categories over $\mathcal D$, whose 1-morphisms are the 1-morphisms of $\mathbf{Cat}/\mathcal D$ preserving strongly cartesian morphisms, and whose 2-morphisms are all 2-morphisms of $\mathbf{Cat}/\mathcal D$ between such 1-morphisms.
--
--   **Statement.** Let $\mathcal D$ be a category, let $\mathcal X,\mathcal Y,\mathcal S$ be fibered categories over $\mathcal D$, and let $F:\mathcal X\to\mathcal S$ and $G:\mathcal Y\to\mathcal S$ be 1-morphisms of $\mathbf{Fib}/\mathcal D$. Then there is a 2-fibre product $(P,p_1,p_2,\psi)$ of $(F,G)$ in $\mathbf{Cat}/\mathcal D$ such that:
--
--   1. $P$ is a fibered category over $\mathcal D$;
--   2. the projections $p_1:P\to\mathcal X$ and $p_2:P\to\mathcal Y$ preserve strongly cartesian morphisms;
--   3. for every 2-commutative square $(Q,c,d,\chi)$ over $(F,G)$ in $\mathbf{Cat}/\mathcal D$ with $Q$ fibered over $\mathcal D$ and $c,d$ preserving strongly cartesian morphisms, and every morphism of squares $(k,\alpha,\beta):(Q,c,d,\chi)\to(P,p_1,p_2,\psi)$, the 1-morphism $k:Q\to P$ preserves strongly cartesian morphisms.
--
--   By 1 and 2 the square $(P,p_1,p_2,\psi)$ lies in $\mathbf{Fib}/\mathcal D$, and by 3 its universal property in $\mathbf{Cat}/\mathcal D$ restricts to $\mathbf{Fib}/\mathcal D$ (the 2-morphisms being the same): it is a 2-fibre product of $(F,G)$ in $\mathbf{Fib}/\mathcal D$ and in the associated strict $(2,1)$-category $(\mathbf{Fib}/\mathcal D)^{\mathrm{strict}}$. In other words $(\mathbf{Fib}/\mathcal D)^{\mathrm{strict}}$ has 2-fibre products and they are computed in $(\mathbf{Cat}/\mathcal D)^{\mathrm{strict}}$. In the source this is the step from categories over a site to fibered categories on the way to 2-fibre products of stacks.
--
--   **Deviation from the source.** Only the first assertion of the source's lemma is formalized; its second assertion (the fibre category of the 2-fibre product over an object $T$ of $\mathcal D$ is the 2-fibre product of the fibre categories, formed in $\mathbf{Cat}$) is not.
--
--   **Formalization Note.** The 2-fibre product predicate is the platform definition `IsWeakTwoPullback` on `TwoPullbackCone f g` (structures `TwoPullbackCone`, `TwoConeMorphism` and predicate `IsWeakTwoPullback` of the definition file `QAlgorithms_Papers_Independent_Intakenext100_P43`, namespace `QAlgorithms.Papers.Independent.Intakenext100.P43`): a cone is `(vertex, first, second, comparison : first ≫ f ≅ second ≫ g)`, and `IsWeakTwoPullback P` says that every cone `A` has a cone morphism `u` to `P` such that for every cone morphism `u'` from `A` to `P` there is a unique 2-isomorphism `u.map ≅ u'.map` compatible with the two comparison cells; since 2-isomorphisms compose and invert, this is equivalent to conditions 1 and 2 above. Lean composes in diagrammatic order (`a ≫ f` is $f\circ a$). $\mathbf{Cat}/\mathcal D$ is Mathlib's bicategory `BasedCategory 𝒮` (objects: a type `obj` with a category structure and a functor `p : obj ⥤ 𝒮`; 1-morphisms: `BasedFunctor`, i.e. functors `F` with `F ⋙ 𝒴.p = 𝒳.p`; 2-morphisms: `BasedNatTrans`, i.e. natural transformations whose components lift identities). The three based categories are taken in `BasedCategory.{v₂, v₂} 𝒮` (objects and morphisms in `Type v₂`), that is, the small categories over $\mathcal D$ of the source; the class is closed under the construction because the objects of the 2-fibre product, which involve isomorphisms of $\mathcal S$, again form a type in the universe of the morphisms. This statement replaces `TwoCategory.basedCategory_exists_isWeakTwoPullback_fibered`, whose objects were taken in `Type (max u₂ v₂)`: there the universe `u₂` occurs only inside a `max`, which prevents the platform from matching any proof against that statement. The base `𝒮` is an arbitrary category (the source takes $\mathcal D$ small). Mathlib has no bicategory of fibered categories, so membership in $\mathbf{Fib}/\mathcal D$ is spelled out: `p.IsFibered` is Mathlib's class of fibered categories (equivalent to the existence of strongly cartesian lifts), `p.IsStronglyCartesian f φ` says that `φ` is a strongly cartesian morphism lying over `f`, and "`K` preserves strongly cartesian morphisms" is the hypothesis `∀ f φ, p.IsStronglyCartesian f φ → p'.IsStronglyCartesian f (K.map φ)`. Lean names: the base category $\mathcal D$ is `𝒮`, the categories $\mathcal X$, $\mathcal Y$ are `𝒳`, `𝒴`, and the common target $\mathcal S$ of $F$ and $G$ is `𝒵` (so the Lean `𝒮` is not the $\mathcal S$ of this text).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 915-916, Lemma E.5.7.9 (first assertion; with Definitions E.5.7.5, E.5.7.7 and Example E.5.7.8); classical reference (cited by the paper): Stacks Project Authors, Stacks Project, Tag 02XQ; D. A. Acosta Álvarez, Some results in quotient stacks, Centro de Investigación en Matemáticas, A.C. (2016), Ch. I, Lemma 1.3.6

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P43

open CategoryTheory CategoryTheory.Limits QAlgorithms.Papers.Independent.Intakenext100.P43

set_option autoImplicit false

universe v₁ u₁ v₂

namespace TwoCategory

theorem smallBasedCategory_exists_isWeakTwoPullback_fibered
    {𝒮 : Type u₁} [Category.{v₁} 𝒮]
    (𝒳 𝒴 𝒵 : BasedCategory.{v₂, v₂} 𝒮)
    (h𝒳 : 𝒳.p.IsFibered) (h𝒴 : 𝒴.p.IsFibered) (h𝒵 : 𝒵.p.IsFibered)
    (F : 𝒳 ⟶ 𝒵) (G : 𝒴 ⟶ 𝒵)
    (hF : ∀ {R S : 𝒮} (f : R ⟶ S) {a b : 𝒳.obj} (φ : a ⟶ b),
      𝒳.p.IsStronglyCartesian f φ → 𝒵.p.IsStronglyCartesian f (F.map φ))
    (hG : ∀ {R S : 𝒮} (f : R ⟶ S) {a b : 𝒴.obj} (φ : a ⟶ b),
      𝒴.p.IsStronglyCartesian f φ → 𝒵.p.IsStronglyCartesian f (G.map φ)) :
    ∃ P : TwoPullbackCone F G, IsWeakTwoPullback P ∧ P.vertex.p.IsFibered ∧
      (∀ {R S : 𝒮} (f : R ⟶ S) {a b : P.vertex.obj} (φ : a ⟶ b),
        P.vertex.p.IsStronglyCartesian f φ → 𝒳.p.IsStronglyCartesian f (P.first.map φ)) ∧
      (∀ {R S : 𝒮} (f : R ⟶ S) {a b : P.vertex.obj} (φ : a ⟶ b),
        P.vertex.p.IsStronglyCartesian f φ → 𝒴.p.IsStronglyCartesian f (P.second.map φ)) ∧
      ∀ (Q : TwoPullbackCone F G), Q.vertex.p.IsFibered →
        (∀ {R S : 𝒮} (f : R ⟶ S) {a b : Q.vertex.obj} (φ : a ⟶ b),
          Q.vertex.p.IsStronglyCartesian f φ → 𝒳.p.IsStronglyCartesian f (Q.first.map φ)) →
        (∀ {R S : 𝒮} (f : R ⟶ S) {a b : Q.vertex.obj} (φ : a ⟶ b),
          Q.vertex.p.IsStronglyCartesian f φ → 𝒴.p.IsStronglyCartesian f (Q.second.map φ)) →
        ∀ (k : TwoConeMorphism Q P) {R S : 𝒮} (f : R ⟶ S) {a b : Q.vertex.obj} (φ : a ⟶ b),
          Q.vertex.p.IsStronglyCartesian f φ →
            P.vertex.p.IsStronglyCartesian f (k.map.map φ) := by sorry

end TwoCategory
