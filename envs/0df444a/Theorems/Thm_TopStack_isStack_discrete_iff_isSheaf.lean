-- Prove2me | Theorems.Thm_TopStack_isStack_discrete_iff_isSheaf
-- name    : TopStack.isStack_discrete_iff_isSheaf
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T17:00:59.168885+00:00
-- url     : https://prove2.me/theorems/4698cb40-6026-4ca6-9a28-f114fc821cce
-- title:
--   A presheaf of sets, viewed as a pseudofunctor into discrete categories, is a stack if and only if it is a sheaf
-- statement:
--   **Stacks fibered in sets are sheaves of sets.** A presheaf of sets on a site, regarded as a pseudofunctor with values in discrete categories, is a stack exactly when it is a sheaf.
--
--   Let $\mathcal C$ be a category equipped with a Grothendieck topology $J$, and let $P:\mathcal C^{\mathrm{op}}\to\mathbf{Sets}$ be a presheaf of sets. Let $\underline P:\mathcal C^{\mathrm{op}}\to\mathbf{Cat}$ be the (strict) pseudofunctor sending an object $T$ to the discrete category on the set $P(T)$ and a morphism $f:T'\to T$ to the functor induced by the map $P(f):P(T)\to P(T')$; its Grothendieck construction is the split category fibered in sets $\mathcal S_P\to\mathcal C$ of Construction E.6.1.1 and Lemma E.6.1.2(2). Recall that a pseudofunctor $F:\mathcal C^{\mathrm{op}}\to\mathbf{Cat}$ is a *stack* for $J$ if
--
--   1. for every object $T$ and all objects $x,y$ of $F(T)$, the presheaf $\mathrm{Isom}(x,y)$ (more precisely $\mathrm{Hom}(x,y)$) on $\mathcal C/T$, $(f:T'\to T)\mapsto \mathrm{Hom}_{F(T')}(f^*x,f^*y)$, is a sheaf for the induced topology, and
--   2. for every object $T$ and every $J$-covering sieve $R$ of $T$, every descent datum relative to $R$ is effective, i.e. the functor from $F(T)$ to the category of descent data relative to $R$ is essentially surjective (hence an equivalence).
--
--   The theorem states:
--   $$\underline P \text{ is a stack for } J\iff P \text{ is a sheaf of sets for } J.$$
--
--   In particular, if $J$ is subcanonical, then for every object $X$ of $\mathcal C$ the representable presheaf $h_X=\mathrm{Hom}_{\mathcal C}(-,X)$ is a sheaf, so the split fibered category $\underline X=\mathcal S_{h_X}$ is a stack in groupoids. This is the observation made in Remark E.6.2.5 for the site $\mathbf{CGWH}_{\alpha,\tau}$ of compactly generated weakly Hausdorff spaces, whose topology is subcanonical: it is how every space $X$ is regarded as a stack $\underline X$ (equivalently $\mathcal S_X$), the starting point for the charts $\underline X\to[X/\mathcal R]$ of quotient stacks. Conversely, the equivalence identifies stacks fibered in sets with sheaves of sets.
--
--   **Formalization Note.** $\underline P$ is `(P ⋙ typeToCat).toPseudofunctor'`, where `typeToCat` sends a type to its discrete category; "stack" is Mathlib's `Pseudofunctor.IsStack J` (tagged Stacks Project Tag 026F, the reference the paper gives for Definition E.6.1.6 in Remark E.6.1.7), which is formulated for pseudofunctors rather than for their Grothendieck constructions; "sheaf" is `Presieve.IsSheaf J P`. The statement is made for an arbitrary site and an arbitrary universe of the presheaf; the paper's situation is $\mathcal C=\mathbf{CGWH}_{\alpha}$ with its $\tau$-topology and $P=h_X$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 923, Remark E.6.2.5 (with Construction E.6.1.1 and Lemma E.6.1.2(2), pp. 920-921, and Definition E.6.1.6, p. 922); classical reference: the paper cites the Stacks Project, Tag 026F, for the definition of a stack (Remark E.6.1.7)

import Mathlib

open CategoryTheory

set_option autoImplicit false

universe w v u

namespace TopStack

theorem isStack_discrete_iff_isSheaf {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (P : Cᵒᵖ ⥤ Type w) :
    (P ⋙ typeToCat.{w}).toPseudofunctor'.IsStack J ↔ Presieve.IsSheaf J P := by sorry

end TopStack
