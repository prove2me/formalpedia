-- Prove2me | Theorems.Thm_TwoCategory_basedCategory_hasPullbacks
-- name    : TwoCategory.basedCategory_hasPullbacks
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:23:40.095437+00:00
-- url     : https://prove2.me/theorems/0836693c-714c-4acd-815a-dec2bc126146
-- title:
--   The category of categories over a category $\mathcal D$ has fibre products (1-fibre products in $\mathbf{Cat}/\mathcal D$)
-- statement:
--   Existence of strict (1-categorical) fibre products of categories over a fixed base category.
--
--   **Categories over $\mathcal D$.** Let $\mathcal D$ be a category. A *category over $\mathcal D$* is a pair $(\mathcal S,p)$ of a category $\mathcal S$ and a functor $p:\mathcal S\to\mathcal D$. The 2-category $\mathbf{Cat}/\mathcal D$ (Example E.5.7.2 of the source) has the categories over $\mathcal D$ as objects; its 1-morphisms $(\mathcal S,p)\to(\mathcal S',p')$ are the functors $F:\mathcal S\to\mathcal S'$ with $p'\circ F=p$ (equality of functors), and its 2-morphisms $t:F\Rightarrow F'$ are the natural transformations with $p'(t_A)=1_{p(A)}$ for every object $A$ of $\mathcal S$.
--
--   For a 2-category $\mathcal C$ let $\mathrm{Cat}(\mathcal C)$ be the ordinary category with the same objects whose morphisms are the 1-morphisms of $\mathcal C$ (Construction E.5.2.6). A *1-fibre product* of two 1-morphisms $f:B\to A$, $g:C\to A$ of $\mathcal C$ is a fibre product of $(f,g)$ in the ordinary category $\mathrm{Cat}(\mathcal C)$ (Definition E.5.7.14).
--
--   **Statement.** Let $\mathcal D$ be a category. The 2-category $\mathbf{Cat}/\mathcal D$ has 1-fibre products: for all 1-morphisms $F:\mathcal X\to\mathcal S$ and $G:\mathcal Y\to\mathcal S$ of categories over $\mathcal D$ the fibre product
--
--   $$\mathcal X\times^1_{F,\mathcal S,G}\mathcal Y$$
--
--   exists in the ordinary category of categories over $\mathcal D$ and functors over $\mathcal D$.
--
--   Explicitly, $\mathcal X\times^1_{F,\mathcal S,G}\mathcal Y$ has as objects the pairs $(x,y)$ with $F(x)=G(y)$ and as morphisms the pairs $(a,b)$ with $F(a)=G(b)$, with composition defined componentwise. In contrast with the 2-fibre product, objects are required to have *equal* images in $\mathcal S$; the source uses 1-fibre products to compute stack-theoretic intersections of "graph" and "diagonal" substacks.
--
--   **Formalization Note.** $\mathrm{Cat}(\mathbf{Cat}/\mathcal D)$ is Mathlib's category structure on `BasedCategory.{v₂, u₂} 𝒮` (objects: a type `obj : Type u₂` with a category structure with morphisms in `Type v₂` and a functor `p : obj ⥤ 𝒮`; morphisms: `BasedFunctor`, i.e. functors `F` with `F ⋙ 𝒴.p = 𝒳.p`), and the statement is `Limits.HasPullbacks` for it. Here no relation between the universes `u₂`, `v₂` is needed, and the base `𝒮` is an arbitrary category (the source takes $\mathcal D$ small).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 917, Lemma E.5.7.16 (with Definition E.5.7.14 and Construction E.5.2.6, p. 902); classical reference (cited by the paper in the proof): D. A. Acosta Álvarez, Some results in quotient stacks, Centro de Investigación en Matemáticas, A.C. (2016), Ch. I, Lemma 1.2.3

import Mathlib

open CategoryTheory

set_option autoImplicit false

universe v₁ u₁ v₂ u₂

namespace TwoCategory

theorem basedCategory_hasPullbacks {𝒮 : Type u₁} [Category.{v₁} 𝒮] :
    Limits.HasPullbacks (BasedCategory.{v₂, u₂} 𝒮) := by sorry

end TwoCategory
