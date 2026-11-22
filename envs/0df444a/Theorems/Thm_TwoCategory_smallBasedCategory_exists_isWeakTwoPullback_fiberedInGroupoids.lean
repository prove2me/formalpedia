-- Prove2me | Theorems.Thm_TwoCategory_smallBasedCategory_exists_isWeakTwoPullback_fiberedInGroupoids
-- name    : TwoCategory.smallBasedCategory_exists_isWeakTwoPullback_fiberedInGroupoids
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T16:29:35.56413+00:00
-- url     : https://prove2.me/theorems/0a91d053-95e6-47b5-8243-1350e2c62475
-- title:
--   2-fibre products of small categories fibered in groupoids over $\mathcal D$ exist and are computed in $\mathbf{Cat}/\mathcal D$
-- statement:
--   Existence of 2-fibre products of categories fibered in groupoids over a base category, computed as 2-fibre products of categories over the base.
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
--   is a bijection. The category $(\mathcal S,p)$ is *fibered over $\mathcal D$* (Definition E.5.7.7) if for every object $a$ of $\mathcal S$ and every morphism $f:U\to p(a)$ of $\mathcal D$ there is a strongly cartesian morphism $\varphi:f^*a\to a$ with $p(\varphi)=f$.
--
--   For an object $U$ of $\mathcal D$ the *fibre category* $\mathcal S_U$ has as objects the objects $a$ of $\mathcal S$ with $p(a)=U$ and as morphisms the morphisms $\varphi$ of $\mathcal S$ with $p(\varphi)=1_U$. The category $(\mathcal S,p)$ is *fibered in groupoids over $\mathcal D$* if it is fibered over $\mathcal D$ and all its fibre categories $\mathcal S_U$ are groupoids (Example E.5.7.10). The strict $(2,1)$-category $\mathbf{Groupoids}/\mathcal D$ has these as objects, the functors over $\mathcal D$ as 1-morphisms, and the 2-isomorphisms of $\mathbf{Cat}/\mathcal D$ between them as 2-morphisms.
--
--   **Statement.** Let $\mathcal D$ be a category, let $\mathcal X,\mathcal Y,\mathcal S$ be categories fibered in groupoids over $\mathcal D$, and let $F:\mathcal X\to\mathcal S$, $G:\mathcal Y\to\mathcal S$ be functors over $\mathcal D$. Then there is a 2-fibre product $(P,p_1,p_2,\psi)$ of $(F,G)$ in $\mathbf{Cat}/\mathcal D$ such that $P$ is fibered in groupoids over $\mathcal D$.
--
--   Since $\mathbf{Groupoids}/\mathcal D$ is a full sub-2-category of $(\mathbf{Cat}/\mathcal D)^{\mathrm{strict}}$, such a square is a 2-fibre product of $(F,G)$ in $\mathbf{Groupoids}/\mathcal D$: this 2-category has 2-fibre products and they are computed in $(\mathbf{Cat}/\mathcal D)^{\mathrm{strict}}$. For $\mathcal D=\mathbf 1$ this gives the 2-fibre products of groupoids; in the source the statement is the last step before the 2-fibre products of stacks in groupoids on a site (obtained by stackification).
--
--   **Formalization Note.** The 2-fibre product predicate is the platform definition `IsWeakTwoPullback` on `TwoPullbackCone f g` (structures `TwoPullbackCone`, `TwoConeMorphism` and predicate `IsWeakTwoPullback` of the definition file `QAlgorithms_Papers_Independent_Intakenext100_P43`, namespace `QAlgorithms.Papers.Independent.Intakenext100.P43`): a cone is `(vertex, first, second, comparison : first ≫ f ≅ second ≫ g)`, and `IsWeakTwoPullback P` says that every cone `A` has a cone morphism `u` to `P` such that for every cone morphism `u'` from `A` to `P` there is a unique 2-isomorphism `u.map ≅ u'.map` compatible with the two comparison cells; since 2-isomorphisms compose and invert, this is equivalent to conditions 1 and 2 above. Lean composes in diagrammatic order (`a ≫ f` is $f\circ a$). $\mathbf{Cat}/\mathcal D$ is Mathlib's bicategory `BasedCategory 𝒮` (objects: a type `obj` with a category structure and a functor `p : obj ⥤ 𝒮`; 1-morphisms: `BasedFunctor`, i.e. functors `F` with `F ⋙ 𝒴.p = 𝒳.p`; 2-morphisms: `BasedNatTrans`, i.e. natural transformations whose components lift identities). The three based categories are taken in `BasedCategory.{v₂, v₂} 𝒮` (objects and morphisms in `Type v₂`), that is, the small categories over $\mathcal D$ of the source; the class is closed under the construction because the objects of the 2-fibre product, which involve isomorphisms of $\mathcal S$, again form a type in the universe of the morphisms. This statement replaces `TwoCategory.basedCategory_exists_isWeakTwoPullback_fiberedInGroupoids`, whose objects were taken in `Type (max u₂ v₂)`: there the universe `u₂` occurs only inside a `max`, which prevents the platform from matching any proof against that statement. The base `𝒮` is an arbitrary category (the source takes $\mathcal D$ small). "Fibered in groupoids" is expressed with Mathlib notions as `p.IsFibered` together with `∀ S, IsGroupoid (p.Fiber S)`, where `p.Fiber S` is Mathlib's fibre category. The source defines $\mathbf{Groupoids}/\mathcal D$ as a full sub-2-category of $\mathbf{Fib}/\mathcal D$, whose 1-morphisms are required to preserve strongly cartesian morphisms; in a category fibered in groupoids every morphism is strongly cartesian, so this requirement is automatic and `F`, `G` range over all 1-morphisms of `BasedCategory 𝒮`. Lean names: the base category $\mathcal D$ is `𝒮`, the categories $\mathcal X$, $\mathcal Y$ are `𝒳`, `𝒴`, and the common target $\mathcal S$ of $F$ and $G$ is `𝒵` (so the Lean `𝒮` is not the $\mathcal S$ of this text).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 916, Lemma E.5.7.11 (with Example E.5.7.10); classical reference (cited by the paper): Stacks Project Authors, Stacks Project, Tag 0041; D. A. Acosta Álvarez, Some results in quotient stacks, Centro de Investigación en Matemáticas, A.C. (2016), Ch. I, Lemma 1.5.3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P43

open CategoryTheory CategoryTheory.Limits QAlgorithms.Papers.Independent.Intakenext100.P43

set_option autoImplicit false

universe v₁ u₁ v₂

namespace TwoCategory

theorem smallBasedCategory_exists_isWeakTwoPullback_fiberedInGroupoids
    {𝒮 : Type u₁} [Category.{v₁} 𝒮]
    (𝒳 𝒴 𝒵 : BasedCategory.{v₂, v₂} 𝒮)
    (h𝒳 : 𝒳.p.IsFibered) (h𝒳' : ∀ S : 𝒮, IsGroupoid (𝒳.p.Fiber S))
    (h𝒴 : 𝒴.p.IsFibered) (h𝒴' : ∀ S : 𝒮, IsGroupoid (𝒴.p.Fiber S))
    (h𝒵 : 𝒵.p.IsFibered) (h𝒵' : ∀ S : 𝒮, IsGroupoid (𝒵.p.Fiber S))
    (F : 𝒳 ⟶ 𝒵) (G : 𝒴 ⟶ 𝒵) :
    ∃ P : TwoPullbackCone F G, IsWeakTwoPullback P ∧ P.vertex.p.IsFibered ∧
      ∀ S : 𝒮, IsGroupoid (P.vertex.p.Fiber S) := by sorry

end TwoCategory
