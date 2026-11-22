-- Prove2me | Theorems.Thm_TopStack_Inertia_forget_isEquivalence_iff
-- name    : TopStack.Inertia.forget_isEquivalence_iff
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T17:02:07.974735+00:00
-- url     : https://prove2.me/theorems/5fa877bc-67cf-4850-b5a2-afacdacfc6b8
-- title:
--   The inertia is trivial ($\iota:\mathcal I_{\mathcal X}\to\mathcal X$ is an equivalence) iff every automorphism lying over an identity is the identity
-- statement:
--   **Criterion for trivial inertia.** Let $\mathcal S$ be a category, $p:\mathcal X\to\mathcal S$ a functor (for instance a stack in groupoids over a site), $\mathcal I_{\mathcal X}$ its inertia category (objects: pairs $(x,f)$ with $f$ an automorphism of $x$ such that $p(f)=\mathrm{id}_{p(x)}$; morphisms $(x,f)\to(y,g)$: morphisms $\phi:x\to y$ with $\phi\circ f=g\circ\phi$) and $\iota:\mathcal I_{\mathcal X}\to\mathcal X$, $(x,f)\mapsto x$, the canonical functor. Then the following are equivalent:
--
--   1. $\iota:\mathcal I_{\mathcal X}\to\mathcal X$ is an equivalence of categories (the inertia of $\mathcal X$ is *trivial*);
--   2. every automorphism lying over an identity is trivial: for every object $x$ of $\mathcal X$ and every automorphism $f$ of $x$,
--   $$p(f)=\mathrm{id}_{p(x)}\ \Longrightarrow\ f=\mathrm{id}_x .$$
--
--   Terminology E.6.3.1 calls the inertia of a stack $\mathcal X$ trivial when $\iota$ is an equivalence and announces that this means that all inertia groups of $\mathcal X$ at all points are trivial; condition 2 says exactly that all the automorphism groups $\{f\in\mathrm{Aut}(x): p(f)=\mathrm{id}\}$ are trivial. Trivial inertia is the conclusion of Lemma E.6.3.7 (quotient stacks of topological groupoids with injective $(s,t):\mathcal G\to X\times X$) and is used in the proof of the representability criterion Proposition E.6.3.8.
--
--   **Formalization Note.** $\mathcal I_{\mathcal X}$ and $\iota$ are `TopStack.Inertia p` and `TopStack.Inertia.forget p` (definition `TopStack_Inertia`); "equivalence" is Mathlib's `Functor.IsEquivalence` (fully faithful and essentially surjective). No hypothesis on $p$ is needed; when condition 2 holds, $\iota$ is even an isomorphism of categories over $\mathcal S$ with inverse $x\mapsto(x,\mathrm{id}_x)$ (the section $\varepsilon$ of Remark E.6.3.3), so the equivalence also holds in the 2-category of categories over $\mathcal S$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 925, Terminology E.6.3.1 (with Remark E.6.3.3 and Definition E.6.3.1, pp. 924-925)

import Mathlib
import Definitions.Def_TopStack_Inertia

open CategoryTheory

set_option autoImplicit false

universe v₁ u₁ v₂ u₂

namespace TopStack

theorem Inertia.forget_isEquivalence_iff {𝒮 : Type u₁} [Category.{v₁} 𝒮]
    {𝒳 : Type u₂} [Category.{v₂} 𝒳] (p : 𝒳 ⥤ 𝒮) :
    (Inertia.forget p).IsEquivalence ↔
      ∀ (x : 𝒳) (f : x ≅ x), p.map f.hom = 𝟙 (p.obj x) → f.hom = 𝟙 x := by sorry

end TopStack
