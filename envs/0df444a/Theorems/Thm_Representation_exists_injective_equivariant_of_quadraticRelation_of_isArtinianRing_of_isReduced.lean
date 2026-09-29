-- Prove2me | Theorems.Thm_Representation_exists_injective_equivariant_of_quadraticRelation_of_isArtinianRing_of_isReduced
-- name    : Representation.exists_injective_equivariant_of_quadraticRelation_of_isArtinianRing_of_isReduced
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/46da6873-f9ae-592d-a511-d323701e2852
-- title:
--   Boston–Lenstra–Ribet embedding over a reduced Artinian ℚ-algebra
-- statement:
--   Let $k$ be a commutative ring that is Artinian, reduced, and an algebra over $\mathbb{Q}$, and let $G$ be a group. Let $V$ be a $k$-module that is free and finite over $k$ with $\operatorname{finrank}_k V = 2$, equipped with a monoid homomorphism $\rho_V \colon G \to \operatorname{End}_k(V)$ whose image spans $\operatorname{End}_k(V)$ as a $k$-module, i.e. $\operatorname{span}_k(\operatorname{range} \rho_V) = \top$. Let $M$ be a finite $k$-module which is faithful in the sense that any $x \in k$ with $x \cdot m = 0$ for all $m \in M$ vanishes, equipped with a monoid homomorphism $\rho_M \colon G \to \operatorname{End}_k(M)$, and let $d \colon G \to k^\times$ be a group homomorphism. Assume the quadratic relation $$\rho_M(g)^2 - \operatorname{tr}\big(\rho_V(g)\big)\,\rho_M(g) + d(g)\cdot \mathrm{id}_M = 0 \quad \text{in } \operatorname{End}_k(M)$$ for every $g \in G$, where the trace is that of $\rho_V(g)$ on $V$ over $k$. Then there exists a $k$-linear map $j \colon V \to M$ that is injective and satisfies $j(\rho_V(g)v) = \rho_M(g)(j(v))$ for all $g \in G$ and $v \in V$.
--
--   This is the Boston–Lenstra–Ribet embedding lemma in the form used by Wiles, at the level of a reduced Artinian $\mathbb{Q}$-algebra of coefficients: a module satisfying the quadratic relation attached to a two-dimensional representation whose image spans the endomorphism algebra contains that representation. It is the intermediate step towards the version for a faithful module over a general reduced coefficient ring, [`Representation.exists_injective_equivariant_of_quadraticRelation_of_faithful_of_isReduced`](thm.html#Representation.exists_injective_equivariant_of_quadraticRelation_of_faithful_of_isReduced), and relies on the decomposition of $k$ into a finite product of characteristic-zero fields together with the direct-sum decomposition over each factor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Representation_exists_injective_equivariant_of_quadraticRelation_of_isArtinianRing_of_isReduced.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Representation.exists_injective_equivariant_of_quadraticRelation_of_isArtinianRing_of_isReduced
    {k : Type} [CommRing k] [IsArtinianRing k] [IsReduced k] [Algebra ℚ k]
    {G : Type} [Group G]
    {V : Type} [AddCommGroup V] [Module k V] [Module.Free k V] [Module.Finite k V] (hV : Module.finrank k V = 2)
    (ρV : G →* Module.End k V) (hspan : Submodule.span k (Set.range ⇑ρV) = ⊤)
    {M : Type} [AddCommGroup M] [Module k M] [Module.Finite k M]
    (hfaith : ∀ x : k, (∀ m : M, x • m = 0) → x = 0)
    (ρM : G →* Module.End k M) (d : G →* kˣ)
    (hrel : ∀ g : G,
      ρM g * ρM g - (LinearMap.trace k V (ρV g)) • ρM g + ((d g : kˣ) : k) • (1 : Module.End k M) = 0) :
    ∃ j : V →ₗ[k] M, Function.Injective j ∧ ∀ (g : G) (v : V), j (ρV g v) = ρM g (j v) := by sorry
