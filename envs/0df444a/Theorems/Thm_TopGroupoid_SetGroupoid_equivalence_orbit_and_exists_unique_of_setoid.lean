-- Prove2me | Theorems.Thm_TopGroupoid_SetGroupoid_equivalence_orbit_and_exists_unique_of_setoid
-- name    : TopGroupoid.SetGroupoid.equivalence_orbit_and_exists_unique_of_setoid
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:32:41.113374+00:00
-- url     : https://prove2.me/theorems/0bdd87bc-bd39-490d-a298-0fc4e754ec16
-- title:
--   The image of $(t,s):R\to X\times X$ for a groupoid is an equivalence relation on $X$, and every equivalence relation is the image of a groupoid with $(t,s)$ injective, unique up to isomorphism
-- statement:
--   Groupoids generalize equivalence relations: the pairs of objects joined by a morphism form an equivalence relation, and equivalence relations are exactly the groupoids with at most one morphism between two objects.
--
--   Conventions. A *groupoid in sets* $(X,R,s,t,c,e,i)$ consists of a set $X$ of objects, a set $R$ of morphisms, source and target maps $s,t:R\to X$, a composition law $c:R\times_{s,X,t}R\to R$ defined on the set $R\times_{s,X,t}R=\{(g,h)\in R\times R:\ s(g)=t(h)\}$ of composable pairs, a unit section $e:X\to R$ and an inversion $i:R\to R$, such that $t(c(g,h))=t(g)$, $s(c(g,h))=s(h)$, $c(g,c(h,k))=c(c(g,h),k)$, $s(e(x))=t(e(x))=x$, $c(g,e(s(g)))=g=c(e(t(g)),g)$, $s(i(g))=t(g)$, $t(i(g))=s(g)$, $c(g,i(g))=e(t(g))$ and $c(i(g),g)=e(s(g))$. An element $g\in R$ is thought of as a morphism from $s(g)$ to $t(g)$, and $c(g,h)$ as the composite of $h$ followed by $g$.
--
--   **Statement.** Let $X$ be a set.
--
--   1. For every groupoid in sets $(X,R,s,t,c,e,i)$, the image of the map $$(t,s):R\to X\times X,\qquad g\mapsto(t(g),s(g)),$$ is an equivalence relation on $X$: the relation "there is $g\in R$ with $t(g)=x$ and $s(g)=y$" is reflexive, symmetric and transitive.
--   2. Conversely, for every equivalence relation $E\subseteq X\times X$ there is a groupoid in sets $(X,E,s,t,c,e,i)$ with set of morphisms $E$ whose target and source maps are the two projections, $t(x,y)=x$ and $s(x,y)=y$; for it $(t,s):E\to X\times X$ is the inclusion, which is injective with image $E$.
--   3. Such a groupoid is unique up to isomorphism: if $(X,R_1,\dots)$ and $(X,R_2,\dots)$ are two groupoids in sets with the same set of objects $X$, for both of which $(t,s)$ is injective, and whose maps $(t,s)$ have the same image in $X\times X$, then there is a bijection $\varphi:R_1\to R_2$ such that $(\mathrm{id}_X,\varphi)$ is a morphism of groupoids.
--
--   The paper states this to explain in which sense (topological) groupoids generalize (topological) equivalence relations, the quotient by a non-closed or non-immersed relation being replaced by a quotient stack. Note the order: the first component is the target.
--
--   **Formalization Note.** One conjunction of the three parts, for a fixed type `X`. In part 2 the equivalence relation is a `Setoid X` and the set of morphisms is the subtype `{p : X × X // r p.1 p.2}`. In part 3 "same image" is expressed as the equivalence of the two relations `∃ g, tgt g = x ∧ src g = y`, and the isomorphism as an equivalence `φ : R₁ ≃ R₂` with `G₁.IsHom G₂ id φ` (`SetGroupoid.IsHom` is the notion of morphism of groupoids of the definition file `TopGroupoid_TopologicalGroupoid`).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 887-888, Remark E.4.2.8(1)

import Definitions.Def_TopGroupoid_TopologicalGroupoid

set_option autoImplicit false

universe u v v'

namespace TopGroupoid

theorem SetGroupoid.equivalence_orbit_and_exists_unique_of_setoid {X : Type u} :
    (∀ (R : Type v) (G : SetGroupoid X R),
        Equivalence (fun x y : X => ∃ g : R, G.tgt g = x ∧ G.src g = y)) ∧
      (∀ r : Setoid X, ∃ G : SetGroupoid X {p : X × X // r p.1 p.2},
        (∀ p : {p : X × X // r p.1 p.2}, G.tgt p = p.1.1) ∧
          ∀ p : {p : X × X // r p.1 p.2}, G.src p = p.1.2) ∧
      ∀ (R₁ : Type v) (R₂ : Type v') (G₁ : SetGroupoid X R₁) (G₂ : SetGroupoid X R₂),
        Function.Injective (fun g : R₁ => (G₁.tgt g, G₁.src g)) →
        Function.Injective (fun g : R₂ => (G₂.tgt g, G₂.src g)) →
        (∀ x y : X, (∃ g : R₁, G₁.tgt g = x ∧ G₁.src g = y) ↔
          ∃ g : R₂, G₂.tgt g = x ∧ G₂.src g = y) →
        ∃ φ : R₁ ≃ R₂, G₁.IsHom G₂ id φ := by sorry

end TopGroupoid
