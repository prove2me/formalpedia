-- Prove2me | Theorems.Thm_TopStack_coGrothendieck_fiberedInSets
-- name    : TopStack.coGrothendieck_fiberedInSets
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T17:01:01.336285+00:00
-- url     : https://prove2.me/theorems/2953a4d1-71e5-4cf5-82f1-2a439d622e61
-- title:
--   The Grothendieck construction of a pseudofunctor with discrete values is fibered in sets
-- statement:
--   **Split fibered categories of set-valued pseudofunctors are fibered in sets.** The Grothendieck construction of a pseudofunctor whose values are discrete categories is a fibered category with discrete fibres.
--
--   Let $\mathcal S$ be a category and $F:\mathcal S^{\mathrm{op}}\to\mathbf{Cat}$ a pseudofunctor such that every category $F(U)$ is *discrete*: between two objects there is at most one morphism, and there is none unless the objects are equal (this is the case when $F$ factors through the inclusion $\mathbf{Sets}\to\mathbf{Cat}$ sending a set to the discrete category on it). Let $p_F:\mathcal S_F\to\mathcal S$ be its Grothendieck construction (objects $(U,x)$ with $x\in F(U)$, morphisms $(\phi,f):(U',x')\to(U,x)$ with $\phi:U'\to U$ and $f:x'\to F(\phi)(x)$, $p_F(U,x)=U$). Then
--
--   1. $p_F$ is a fibered category, and
--   2. for every object $U$ of $\mathcal S$ the fibre category $(\mathcal S_F)_U$ (objects over $U$, morphisms over $\mathrm{id}_U$) is discrete;
--
--   that is, $(\mathcal S_F,p_F)$ is a category fibered in sets.
--
--   This is Lemma E.6.1.2(2); it applies to $F=h_X$ and gives the category $\underline X\to\mathbf{CGWH}_{\alpha,\tau}$ fibered in sets attached to a space $X$ (Definition E.6.2.4(5), Remark E.6.2.5).
--
--   **Formalization Note.** Mathlib's `Pseudofunctor.CoGrothendieck`, `CoGrothendieck.forget`, `Functor.IsFibered`, `Functor.Fiber` and `IsDiscrete` (at most one morphism between two objects, and a morphism only between equal objects) are used; "factors through $\mathbf{Sets}\to\mathbf{Cat}$" is rendered as "every $F(U)$ is discrete". Part 1 is a Mathlib instance, included so that the conclusion is the full notion "fibered in sets". The paper states the lemma for a strict pseudo-functor on $\mathbf{CGWH}_{\alpha,\tau}^{\mathrm{opp}}$; it is stated here for an arbitrary base category and pseudofunctor.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 921, Lemma E.6.1.2(2) (with Construction E.6.1.1, p. 920); classical reference: the paper cites the Stacks Project, Tags 003V and 02Y2

import Mathlib

open CategoryTheory

set_option autoImplicit false

universe v₁ u₁ v₂ u₂

namespace TopStack

theorem coGrothendieck_fiberedInSets {𝒮 : Type u₁} [Category.{v₁} 𝒮]
    (F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂})
    (hF : ∀ S : 𝒮, IsDiscrete (F.obj ⟨Opposite.op S⟩)) :
    (Pseudofunctor.CoGrothendieck.forget F).IsFibered ∧
      ∀ S : 𝒮, IsDiscrete ((Pseudofunctor.CoGrothendieck.forget F).Fiber S) := by sorry

end TopStack
