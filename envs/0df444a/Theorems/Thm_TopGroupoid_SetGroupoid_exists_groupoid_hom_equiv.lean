-- Prove2me | Theorems.Thm_TopGroupoid_SetGroupoid_exists_groupoid_hom_equiv
-- name    : TopGroupoid.SetGroupoid.exists_groupoid_hom_equiv
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:32:28.340838+00:00
-- url     : https://prove2.me/theorems/17b1c2b1-d164-4750-ae29-a7fb1342411e
-- title:
--   A groupoid in sets $(X,R,s,t,c,e,i)$ is a category with objects $X$ and $\mathrm{Hom}(x,y)=s^{-1}(x)\cap t^{-1}(y)$ in which every morphism is invertible
-- statement:
--   A groupoid in sets, presented by its structure maps, is the same thing as a small category all of whose morphisms are isomorphisms: this statement constructs the category from the structure maps.
--
--   Conventions. A *groupoid in sets* $(X,R,s,t,c,e,i)$ consists of a set $X$ of objects, a set $R$ of morphisms, source and target maps $s,t:R\to X$, a composition law $c:R\times_{s,X,t}R\to R$ defined on the set $R\times_{s,X,t}R=\{(g,h)\in R\times R:\ s(g)=t(h)\}$ of composable pairs, a unit section $e:X\to R$ and an inversion $i:R\to R$, such that $t(c(g,h))=t(g)$, $s(c(g,h))=s(h)$, $c(g,c(h,k))=c(c(g,h),k)$, $s(e(x))=t(e(x))=x$, $c(g,e(s(g)))=g=c(e(t(g)),g)$, $s(i(g))=t(g)$, $t(i(g))=s(g)$, $c(g,i(g))=e(t(g))$ and $c(i(g),g)=e(s(g))$. An element $g\in R$ is thought of as a morphism from $s(g)$ to $t(g)$, and $c(g,h)$ as the composite of $h$ followed by $g$.
--
--   **Statement.** Let $(X,R,s,t,c,e,i)$ be a groupoid in sets. Then there is a category $\mathcal C_R$ with set of objects $X$ and with $$\mathrm{Hom}_{\mathcal C_R}(x,y)=s^{-1}(x)\cap t^{-1}(y)\qquad(x,y\in X),$$ in which the identity of $x$ is $e(x)$, the composite of $f:x\to y$ followed by $g:y\to z$ is $c(g,f)$, and every morphism $f$ is invertible with inverse $i(f)$. Precisely: there are a groupoid structure (a category structure in which every morphism has an inverse) on $X$ and bijections $\varphi_{x,y}:\mathrm{Hom}(x,y)\to\{g\in R:\ s(g)=x,\ t(g)=y\}$ such that $$\varphi_{x,x}(\mathrm{id}_x)=e(x),\qquad \varphi_{x,z}(g\circ f)=c(\varphi_{y,z}(g),\varphi_{x,y}(f)),\qquad \varphi_{y,x}(f^{-1})=i(\varphi_{x,y}(f))$$ for all $x,y,z\in X$, $f:x\to y$ and $g:y\to z$.
--
--   This is the dictionary between the two standard presentations of a groupoid, which the paper uses freely (for instance to prove that maps compatible with $s,t,c$ are morphisms of groupoids); it connects the structure `TopGroupoid.SetGroupoid` with Mathlib's `CategoryTheory.Groupoid`.
--
--   **Formalization Note.** The conclusion is an existence statement: a term of `CategoryTheory.Groupoid.{v} X` (morphism types in the universe of `R`) together with a family of equivalences `φ x y` between `x ⟶ y` and the subtype `{g : R // G.src g = x ∧ G.tgt g = y}`, compatible with `𝟙`, with `≫` (in Mathlib `f ≫ g` is `f` followed by `g`, which corresponds to `G.comp (g, f)`) and with `Groupoid.inv`. Only the direction that the paper spells out (from the structure maps to the category) is stated.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 885, Remark E.4.1.2(1)

import Definitions.Def_TopGroupoid_TopologicalGroupoid

open CategoryTheory

set_option autoImplicit false

universe u v

namespace TopGroupoid

theorem SetGroupoid.exists_groupoid_hom_equiv {X : Type u} {R : Type v} (G : SetGroupoid X R) :
    ∃ (_ : Groupoid.{v} X) (φ : ∀ x y : X, (x ⟶ y) ≃ {g : R // G.src g = x ∧ G.tgt g = y}),
      (∀ x : X, (φ x x (𝟙 x) : R) = G.unit x) ∧
      (∀ (x y z : X) (f : x ⟶ y) (g : y ⟶ z),
        (φ x z (f ≫ g) : R) =
          G.comp ⟨((φ y z g : R), (φ x y f : R)), (φ y z g).2.1.trans (φ x y f).2.2.symm⟩) ∧
      ∀ (x y : X) (f : x ⟶ y), (φ y x (Groupoid.inv f) : R) = G.inv (φ x y f) := by sorry

end TopGroupoid
