-- Prove2me | Theorems.Thm_Representation_det_eq_of_sq_sub_trace_smul_add_smul_one_eq_zero
-- name    : Representation.det_eq_of_sq_sub_trace_smul_add_smul_one_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/bef9ebfd-c741-5ec6-ae84-df36a87c4c99
-- title:
--   Quadratic relation forces d=detρ_V in characteristic ≠ 2
-- statement:
--   Let $k$ be a field in which $2 \neq 0$, let $G$ be a group, let $V$ be a finite-dimensional $k$-vector space with $\dim_k V = 2$, and let $\rho_V \colon G \to \operatorname{End}_k(V)$ be a monoid homomorphism into the multiplicative monoid of $k$-linear endomorphisms of $V$. Let $M$ be a nonzero $k$-vector space (no finiteness assumed), let $\rho_M \colon G \to \operatorname{End}_k(M)$ be a monoid homomorphism, and let $d \colon G \to k^{\times}$ be a group homomorphism. Assume the quadratic relation
--   $$\rho_M(g)^2 - \operatorname{tr}(\rho_V(g))\,\rho_M(g) + d(g)\cdot \mathrm{id}_M = 0$$
--   in $\operatorname{End}_k(M)$ for every $g \in G$, where $\operatorname{tr}$ is the trace of an endomorphism of $V$ and $d(g)$ acts through its image in $k$. The conclusion is that $\det(\rho_V(g)) = d(g)$ in $k$ for every $g \in G$, the determinant being that of the endomorphism $\rho_V(g)$ of $V$.
--
--   This is the identification of the character $d$ occurring in a quadratic (Cayley–Hamilton type) relation with the determinant of the two-dimensional representation whose trace occurs in the same relation, in the style of the Boston–Lenstra–Ribet analysis of quotients of group rings attached to two-dimensional representations. It is used by [`Representation.exists_injective_equivariant_of_quadraticRelation_of_isArtinianRing_of_isReduced`](thm.html#Representation.exists_injective_equivariant_of_quadraticRelation_of_isArtinianRing_of_isReduced).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Representation_det_eq_of_sq_sub_trace_smul_add_smul_one_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Representation.det_eq_of_sq_sub_trace_smul_add_smul_one_eq_zero
    {k : Type} [Field k] (h2 : (2 : k) ≠ 0) {G : Type} [Group G]
    {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (hV : Module.finrank k V = 2)
    (ρV : G →* Module.End k V)
    {M : Type} [AddCommGroup M] [Module k M] [Nontrivial M]
    (ρM : G →* Module.End k M) (d : G →* kˣ)
    (hrel : ∀ g : G,
      ρM g * ρM g - (LinearMap.trace k V (ρV g)) • ρM g + ((d g : kˣ) : k) • (1 : Module.End k M) = 0) :
    ∀ g : G, LinearMap.det (ρV g) = d g := by sorry
