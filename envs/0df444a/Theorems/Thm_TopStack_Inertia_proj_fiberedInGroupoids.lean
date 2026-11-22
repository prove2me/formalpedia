-- Prove2me | Theorems.Thm_TopStack_Inertia_proj_fiberedInGroupoids
-- name    : TopStack.Inertia.proj_fiberedInGroupoids
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T17:02:03.872435+00:00
-- url     : https://prove2.me/theorems/70b2272d-65b9-47c1-801b-f79595fa4105
-- title:
--   The inertia category of a category fibered in groupoids is fibered in groupoids
-- statement:
--   **The inertia of a category fibered in groupoids is fibered in groupoids.** Let $\mathcal S$ be a category and $p:\mathcal X\to\mathcal S$ a category fibered in groupoids, i.e. $p$ is a fibered category and every fibre category $\mathcal X_U$ (objects over $U$, morphisms over $\mathrm{id}_U$) is a groupoid. Let $\mathcal I_{\mathcal X}$ be the inertia category of $\mathcal X$ (objects: pairs $(x,f)$ with $f$ an automorphism of $x$ such that $p(f)=\mathrm{id}$; morphisms $(x,f)\to(y,g)$: morphisms $\phi:x\to y$ with $\phi\circ f=g\circ\phi$), and $q:\mathcal I_{\mathcal X}\to\mathcal S$, $(x,f)\mapsto p(x)$. Then
--
--   1. $q:\mathcal I_{\mathcal X}\to\mathcal S$ is a fibered category, and
--   2. every fibre category $(\mathcal I_{\mathcal X})_U$ is a groupoid;
--
--   so $\mathcal I_{\mathcal X}$ is again a category fibered in groupoids over $\mathcal S$.
--
--   This is the second assertion of Lemma E.6.3.2, which the paper quotes from the Stacks Project (Tag 034H) for stacks in groupoids over $\mathbf{CGWH}_{\alpha,\tau}$; it is what makes the inertia $\mathcal I_{\mathcal X}$ an object of the same 2-category as $\mathcal X$, so that the canonical 1-morphism $\iota:\mathcal I_{\mathcal X}\to\mathcal X$ and its fibres (the inertia groups) can be studied.
--
--   **Formalization Note.** $\mathcal I_{\mathcal X}$ and $q$ are `TopStack.Inertia p` and `TopStack.Inertia.proj p` (definition `TopStack_Inertia`); "fibered in groupoids" is encoded with Mathlib's `Functor.IsFibered`, `Functor.Fiber` and `IsGroupoid` (the same encoding is used in hypothesis and conclusion). The paper assumes $\mathcal X$ is a stack in groupoids; only the weaker hypothesis that $p$ is fibered in groupoids is used here (the descent conditions play no role). The paper's conclusion "fibered category" is completed by the (true) statement that the fibres are groupoids. The first assertion of Lemma E.6.3.2 (the equivalence $\mathcal I_{\mathcal X}\simeq\mathcal X\times_{\Delta,\mathcal X\times\mathcal X,\Delta}\mathcal X$) is not part of this item.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 924, Lemma E.6.3.2 (second assertion), with Definition E.6.3.1; classical reference: the paper cites the Stacks Project, Tag 034H

import Mathlib
import Definitions.Def_TopStack_Inertia

open CategoryTheory

set_option autoImplicit false

universe v₁ u₁ v₂ u₂

namespace TopStack

theorem Inertia.proj_fiberedInGroupoids {𝒮 : Type u₁} [Category.{v₁} 𝒮]
    {𝒳 : Type u₂} [Category.{v₂} 𝒳] (p : 𝒳 ⥤ 𝒮)
    (hp : p.IsFibered) (hfib : ∀ S : 𝒮, IsGroupoid (p.Fiber S)) :
    (Inertia.proj p).IsFibered ∧ ∀ S : 𝒮, IsGroupoid ((Inertia.proj p).Fiber S) := by sorry

end TopStack
