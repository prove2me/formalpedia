-- Prove2me | Theorems.Thm_TopGroupoid_SetGroupoid_isHom_iff
-- name    : TopGroupoid.SetGroupoid.isHom_iff
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:32:29.69692+00:00
-- url     : https://prove2.me/theorems/d99b37b6-81f7-404a-837c-a9a40aa069f0
-- title:
--   A pair of maps between groupoids compatible with source, target and composition is a morphism of groupoids: units and inverses are automatically preserved
-- statement:
--   To check that a pair of maps is a morphism of groupoids it is enough to check the compatibility with the source maps, the target maps and the composition laws.
--
--   Conventions. A *groupoid in sets* $(X,R,s,t,c,e,i)$ consists of a set $X$ of objects, a set $R$ of morphisms, source and target maps $s,t:R\to X$, a composition law $c:R\times_{s,X,t}R\to R$ defined on the set $R\times_{s,X,t}R=\{(g,h)\in R\times R:\ s(g)=t(h)\}$ of composable pairs, a unit section $e:X\to R$ and an inversion $i:R\to R$, such that $t(c(g,h))=t(g)$, $s(c(g,h))=s(h)$, $c(g,c(h,k))=c(c(g,h),k)$, $s(e(x))=t(e(x))=x$, $c(g,e(s(g)))=g=c(e(t(g)),g)$, $s(i(g))=t(g)$, $t(i(g))=s(g)$, $c(g,i(g))=e(t(g))$ and $c(i(g),g)=e(s(g))$. An element $g\in R$ is thought of as a morphism from $s(g)$ to $t(g)$, and $c(g,h)$ as the composite of $h$ followed by $g$.
--
--   A *morphism of groupoids* from $(X,R,s,t,c,e,i)$ to $(X',R',s',t',c',e',i')$ is a pair of maps $f_1:X\to X'$, $f_2:R\to R'$ such that $s'\circ f_2=f_1\circ s$, $t'\circ f_2=f_1\circ t$, $f_2(c(g,h))=c'(f_2(g),f_2(h))$ for all composable pairs $(g,h)$, $f_2\circ e=e'\circ f_1$ and $f_2\circ i=i'\circ f_2$.
--
--   **Statement.** Let $(X,R,s,t,c,e,i)$ and $(X',R',s',t',c',e',i')$ be groupoids in sets and let $f_1:X\to X'$, $f_2:R\to R'$ be maps. The following are equivalent:
--
--   1. $(f_1,f_2)$ is a morphism of groupoids;
--   2. $f_1$ and $f_2$ satisfy $$s'\circ f_2=f_1\circ s,\qquad t'\circ f_2=f_1\circ t,\qquad f_2(c(g,h))=c'(f_2(g),f_2(h))\ \text{ for all }g,h\in R\text{ with }s(g)=t(h).$$
--
--   In the last identity the right-hand side is defined because the first two identities give $s'(f_2(g))=f_1(s(g))=f_1(t(h))=t'(f_2(h))$. In categorical terms: a map between groupoids that respects composition is a functor, and it automatically respects identities and inverses.
--
--   The paper proves it in order to reduce the verification of the defining compatibilities of a morphism of groupoids to the compatibilities with $(s,t,c)$ only.
--
--   **Formalization Note.** `G.IsHom G' f₁ f₂` is the `Prop`-valued structure of the definition file `TopGroupoid_TopologicalGroupoid` with the five compatibilities. Condition 2 is written as an existential over the two proofs `hs`, `ht` of the compatibilities with source and target, because the statement of the compatibility with composition needs them to form the composable pair `(f₂ g, f₂ h)`; an existential over proofs of propositions is the same as a conjunction.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 885, Lemma E.4.1.3

import Definitions.Def_TopGroupoid_TopologicalGroupoid

set_option autoImplicit false

universe u v u' v'

namespace TopGroupoid

theorem SetGroupoid.isHom_iff {X : Type u} {R : Type v} {X' : Type u'} {R' : Type v'}
    (G : SetGroupoid X R) (G' : SetGroupoid X' R') (f₁ : X → X') (f₂ : R → R') :
    G.IsHom G' f₁ f₂ ↔
      ∃ (hs : ∀ g : R, G'.src (f₂ g) = f₁ (G.src g)) (ht : ∀ g : R, G'.tgt (f₂ g) = f₁ (G.tgt g)),
        ∀ (g h : R) (hgh : G.src g = G.tgt h),
          f₂ (G.comp ⟨(g, h), hgh⟩) =
            G'.comp ⟨(f₂ g, f₂ h), (hs g).trans ((congrArg f₁ hgh).trans (ht h).symm)⟩ := by sorry

end TopGroupoid
