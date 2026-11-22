-- Prove2me | Theorems.Thm_TopStack_coGrothendieck_fiberedInGroupoids
-- name    : TopStack.coGrothendieck_fiberedInGroupoids
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T17:01:02.484967+00:00
-- url     : https://prove2.me/theorems/443d6d73-05f4-470c-a99e-7eab5ed2ccaf
-- title:
--   The Grothendieck construction of a groupoid-valued pseudofunctor $\mathcal S^{\mathrm{op}}\to\mathbf{Cat}$ is fibered in groupoids
-- statement:
--   **Split fibered categories of groupoid-valued pseudofunctors are fibered in groupoids.** The Grothendieck construction of a pseudofunctor with values in groupoids is a category fibered in groupoids.
--
--   Let $\mathcal S$ be a category and $F:\mathcal S^{\mathrm{op}}\to\mathbf{Cat}$ a pseudofunctor (for instance a functor). Its Grothendieck construction $\mathcal S_F$ (Construction E.6.1.1, Construction E.5.7.23) has as objects the pairs $(U,x)$ with $U$ an object of $\mathcal S$ and $x$ an object of $F(U)$, and as morphisms $(U',x')\to(U,x)$ the pairs $(\phi,f)$ with $\phi:U'\to U$ in $\mathcal S$ and $f:x'\to F(\phi)(x)$ in $F(U')$; the projection $p_F:\mathcal S_F\to\mathcal S$ is $p_F(U,x)=U$, $p_F(\phi,f)=\phi$. For an object $U$ of $\mathcal S$, the fibre category $(\mathcal S_F)_U$ has the objects lying over $U$ and the morphisms lying over $\mathrm{id}_U$.
--
--   If $F(U)$ is a groupoid for every object $U$ of $\mathcal S$, then
--
--   1. $p_F:\mathcal S_F\to\mathcal S$ is a fibered category, and
--   2. every fibre category $(\mathcal S_F)_U$ is a groupoid;
--
--   that is, $(\mathcal S_F,p_F)$ is a category fibered in groupoids.
--
--   This is Lemma E.6.1.2(1). It is how the paper produces its prestacks in groupoids over $\mathbf{CGWH}_{\alpha,\tau}$: the split categories $\mathcal S_{(X,\mathcal R)}$, $\mathcal S_{(X,G)}$, $\mathcal S_X$ attached to the functor of points of a topological groupoid (Definition E.6.2.4), whose stackifications are the quotient stacks $[X/\mathcal R]$.
--
--   **Formalization Note.** $\mathcal S_F$ and $p_F$ are Mathlib's `Pseudofunctor.CoGrothendieck F` (notation `∫ᶜ F`) and `Pseudofunctor.CoGrothendieck.forget F`; "fibered" is `Functor.IsFibered` and the fibre category is `Functor.Fiber` (morphisms lying over the identity). Part 1 is already a Mathlib instance and is included only so that the conclusion reads "fibered in groupoids" (fibered with groupoid fibres, the characterization the paper invokes via the Stacks Project, Tag 003V). The paper states the lemma for a strict pseudo-functor on $\mathbf{CGWH}_{\alpha,\tau}^{\mathrm{opp}}$; it is stated here for an arbitrary base category and an arbitrary pseudofunctor. The composition law printed in (E.6.1.3) is garbled; the standard one, (E.5.7.5), is the one used by Mathlib.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 921, Lemma E.6.1.2 and Lemma E.6.1.2(1) (with Construction E.6.1.1, p. 920); classical reference: the paper cites D. A. Acosta Álvarez, Some results in quotient stacks (2016), Ch. I, §1.4, and the Stacks Project, Tags 003V and 02Y2

import Mathlib

open CategoryTheory

set_option autoImplicit false

universe v₁ u₁ v₂ u₂

namespace TopStack

theorem coGrothendieck_fiberedInGroupoids {𝒮 : Type u₁} [Category.{v₁} 𝒮]
    (F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂})
    (hF : ∀ S : 𝒮, IsGroupoid (F.obj ⟨Opposite.op S⟩)) :
    (Pseudofunctor.CoGrothendieck.forget F).IsFibered ∧
      ∀ S : 𝒮, IsGroupoid ((Pseudofunctor.CoGrothendieck.forget F).Fiber S) := by sorry

end TopStack
