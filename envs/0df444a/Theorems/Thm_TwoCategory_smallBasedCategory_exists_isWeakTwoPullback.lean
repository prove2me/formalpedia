-- Prove2me | Theorems.Thm_TwoCategory_smallBasedCategory_exists_isWeakTwoPullback
-- name    : TwoCategory.smallBasedCategory_exists_isWeakTwoPullback
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T16:29:27.125811+00:00
-- url     : https://prove2.me/theorems/162583b9-bead-4e0d-b1a8-a385862d29b1
-- title:
--   The 2-category $\mathbf{Cat}/\mathcal D$ of small categories over a category $\mathcal D$ has 2-fibre products
-- statement:
--   Existence of 2-fibre products in the 2-category of categories over a fixed base category.
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
--   **Statement.** Let $\mathcal D$ be a category and let $F:\mathcal X\to\mathcal S$ and $G:\mathcal Y\to\mathcal S$ be 1-morphisms of categories over $\mathcal D$. Then a 2-fibre product of $(F,G)$ exists in $\mathbf{Cat}/\mathcal D$; equivalently, in the strict $(2,1)$-category $(\mathbf{Cat}/\mathcal D)^{\mathrm{strict}}$.
--
--   An explicit model is the category $\mathcal X\times^2_{F,\mathcal S,G}\mathcal Y$ of quadruples $(U,x,y,\phi)$ with $U$ an object of $\mathcal D$, $x$ and $y$ objects of $\mathcal X$ and $\mathcal Y$ over $U$, and $\phi:F(x)\to G(y)$ an isomorphism of $\mathcal S$ over $1_U$, with morphisms the pairs $(a,b)$ of morphisms of $\mathcal X$ and $\mathcal Y$ over the same morphism of $\mathcal D$ such that $\phi'\circ F(a)=G(b)\circ\phi$; its projections are $p_1(U,x,y,\phi)=x$, $p_2(U,x,y,\phi)=y$ and its 2-isomorphism $\psi:F\circ p_1\Rightarrow G\circ p_2$ has components $\psi_{(U,x,y,\phi)}=\phi$. The source's Construction E.5.7.3 does not state that $\phi$ lies over $1_U$; this is needed for $\psi$ to be a 2-morphism of $\mathbf{Cat}/\mathcal D$ and is how the model is described in [SP, Tag 0040] (the Stacks Project). The statement is the starting point for the 2-fibre products of fibered categories, of categories fibered in groupoids and of stacks on a site used in Appendix E of the source.
--
--   **Deviation from the source.** The source's lemma adds that the 2-fibre product is equivalent to the explicit category above; the formal statement asserts existence only (any two 2-fibre products of the same pair are equivalent; this is the platform problem `QAlgorithms.Papers.Independent.Intakenext100.P43.proposition11_two_pullbacks_equivalent`, currently open, stated with the same definitions).
--
--   **Formalization Note.** The 2-fibre product predicate is the platform definition `IsWeakTwoPullback` on `TwoPullbackCone f g` (structures `TwoPullbackCone`, `TwoConeMorphism` and predicate `IsWeakTwoPullback` of the definition file `QAlgorithms_Papers_Independent_Intakenext100_P43`, namespace `QAlgorithms.Papers.Independent.Intakenext100.P43`): a cone is `(vertex, first, second, comparison : first ≫ f ≅ second ≫ g)`, and `IsWeakTwoPullback P` says that every cone `A` has a cone morphism `u` to `P` such that for every cone morphism `u'` from `A` to `P` there is a unique 2-isomorphism `u.map ≅ u'.map` compatible with the two comparison cells; since 2-isomorphisms compose and invert, this is equivalent to conditions 1 and 2 above. Lean composes in diagrammatic order (`a ≫ f` is $f\circ a$). $\mathbf{Cat}/\mathcal D$ is Mathlib's bicategory `BasedCategory 𝒮` (objects: a type `obj` with a category structure and a functor `p : obj ⥤ 𝒮`; 1-morphisms: `BasedFunctor`, i.e. functors `F` with `F ⋙ 𝒴.p = 𝒳.p`; 2-morphisms: `BasedNatTrans`, i.e. natural transformations whose components lift identities). The three based categories are taken in `BasedCategory.{v₂, v₂} 𝒮` (objects and morphisms in `Type v₂`), that is, the small categories over $\mathcal D$ of the source; the class is closed under the construction because the objects of the 2-fibre product, which involve isomorphisms of $\mathcal S$, again form a type in the universe of the morphisms. This statement replaces `TwoCategory.basedCategory_exists_isWeakTwoPullback`, whose objects were taken in `Type (max u₂ v₂)`: there the universe `u₂` occurs only inside a `max`, which prevents the platform from matching any proof against that statement. The base `𝒮` is an arbitrary category (the source takes $\mathcal D$ small). Lean names: the base category $\mathcal D$ is `𝒮`, the categories $\mathcal X$, $\mathcal Y$ are `𝒳`, `𝒴`, and the common target $\mathcal S$ of $F$ and $G$ is `𝒵` (so the Lean `𝒮` is not the $\mathcal S$ of this text).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 913-915, Lemma E.5.7.4 (with Example E.5.7.2, Construction E.5.7.3 and Definitions E.5.6.1, E.5.6.2); classical reference (cited by the paper): Stacks Project Authors, Stacks Project, Tag 0040; D. A. Acosta Álvarez, Some results in quotient stacks, Centro de Investigación en Matemáticas, A.C. (2016), Ch. I, Lemma 1.2.1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P43

open CategoryTheory CategoryTheory.Limits QAlgorithms.Papers.Independent.Intakenext100.P43

set_option autoImplicit false

universe v₁ u₁ v₂

namespace TwoCategory

theorem smallBasedCategory_exists_isWeakTwoPullback
    {𝒮 : Type u₁} [Category.{v₁} 𝒮]
    (𝒳 𝒴 𝒵 : BasedCategory.{v₂, v₂} 𝒮) (F : 𝒳 ⟶ 𝒵) (G : 𝒴 ⟶ 𝒵) :
    ∃ P : TwoPullbackCone F G, IsWeakTwoPullback P := by sorry

end TwoCategory
